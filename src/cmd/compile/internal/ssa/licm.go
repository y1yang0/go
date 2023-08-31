// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"sort"
)

// ----------------------------------------------------------------------------
// Loop Invariant Code Motion
//
// This pass hoists loop invariants to loop header or sink them into loop exits.
// The main idea behind LICM is to move loop invariant Value outside of the loop,
// so that they are only executed once, instead of being repeatedly executed with
// each iteration of the loop.
//
// Reference:
// https://llvm.org/doxygen/LICM_8cpp_source.html

const MaxLoopBlockSize = 8

type state struct {
	loopnest   *loopnest // the global loopnest
	loop       *loop     // target loop to be optimized out
	loads      []*Value
	stores     []*Value
	invariants map[*Value]bool
	hoisted    map[*Value]bool
}

func printInvariant(val *Value, block *Block, domBlock *Block) {
	fmt.Printf("== Hoist %v(%v) from b%v to b%v in %v\n",
		val.Op.String(), val.String(),
		block.ID, domBlock.ID, block.Func.Name)
	fmt.Printf("  %v\n", val.LongString())
}

// For Load/Store and some special Values they sould be processed separately
// even if they are loop invariants as they may have observable memory side
// effect
func (s *state) hasMemoryAlias(val *Value) bool {
	loads := s.loads
	stores := s.stores
	if val.Op == OpLoad {
		if len(stores) == 0 {
			// good, no other Store at all
			return true
		}
		// Slow path, we need a type-based alias analysis to know whether Load
		// may alias with Stores
		for _, st := range stores {
			loadPtr := val.Args[0]
			storePtr := st.Args[0]
			at := getMemoryAlias(loadPtr, storePtr)
			fmt.Printf("%v == %v with %v in %v\n", at, loadPtr.LongString(), storePtr.LongString(), val.Block.Func.Name)
			if at != NoAlias {
				return false
			}
		}
		return true
	} else if val.Op == OpStore {
		if len(loads) == 0 && len(stores) == 1 /*itself only*/ {
			return true
		}
		for _, v := range append(stores, loads...) {
			ptr := v.Args[0]
			storePtr := val.Args[0]
			at := getMemoryAlias(ptr, storePtr)
			fmt.Printf("%v == %v with %v in %v\n", at, ptr.LongString(), storePtr.LongString(), val.Block.Func.Name)
			if at != NoAlias {
				return false
			}
		}
		return true
	}
	return false
}

// isExecuteUnconditionally checks if Value is guaranteed to execute during loop iterations
// Otherwise, it should not be hoisted. The most common cases are invariants guarded by
// conditional expressions.
func (s *state) isExecuteUnconditionally(val *Value) bool {
	block := val.Block
	sdom := s.loopnest.sdom
	for _, exit := range s.loop.exits {
		if !sdom.IsAncestorEq(block, exit) {
			return false
		}
	}
	return true
}

func hoist(loopnest *loopnest, loop *loop, val *Value) {
	for valIdx, v := range val.Block.Values {
		if val != v {
			continue
		}
		domBlock := loopnest.sdom.Parent(loop.header)
		// if block.Func.pass.debug >= 1 {
		printInvariant(val, val.Block, domBlock)
		// }
		val.moveTo(domBlock, valIdx)
		break
	}
}

func (s *state) markInvariant(loopBlocks []*Block) map[*Value]bool {
	loopValues := make(map[*Value]bool)
	invariants := make(map[*Value]bool)

	s.loads = make([]*Value, 0)
	s.stores = make([]*Value, 0)
	// First, collect all def inside loop
	for _, block := range loopBlocks {
		for _, val := range block.Values {
			loopValues[val] = true
		}
	}

	for _, block := range loopBlocks {
		// If basic block is located in a nested loop rather than directly in the
		// current loop, it will not be processed.
		if s.loopnest.b2l[block.ID] != s.loop {
			continue
		}

		for _, value := range block.Values {
			if value.Op == OpLoad {
				s.loads = append(s.loads, value)
			} else if value.Op == OpStore {
				s.stores = append(s.stores, value)
			} else if value.Op.IsCall() {
				// bail out the compilation if too complicated, for example, loop involves Calls
				// Theoretically we can hoist Call as long as it does not impose any observable
				// side effects, e.g. only reads memory or dont access memory at all, but
				// unfortunate we may run alias analysis in advance to get such facts, that
				// some what heavy for this pass at present, so we give up further motion
				// once loop blocks involve Calls
				return nil
			}

			isInvariant := true
			for _, use := range value.Args {
				if use.Type.IsMemory() {
					// Store Load and other memory value depends on memory value, which is usually represented
					// as the non-loop-invariant memory value, for example, a memory Phi
					// in loops, but this is not true semantically. We need to treat these
					// kind of Store specifically as loop invariants.
					//
					//      v4, v5.... ;; loop invariant
					// 	cond:
					// 		v2 = Phi <mem> v1 v3
					//      v6 = ...
					// 	BlockIf v6 body, exit
					//  body:
					//		v3 (15) = Store <mem> v4 v5 v2
					//  exit:
					// discard last memory value
					continue
				}
				if _, exist := invariants[use]; exist {
					continue
				}
				if _, exist := loopValues[use]; exist {
					isInvariant = false
					break
				}
			}
			if isInvariant {
				invariants[value] = true
			}
		}
	}
	return invariants
}

// tryHoist hoists profitable loop invariant to block that dominates the entire loop.
// Value is considered as loop invariant if all its inputs are defined outside the loop
// or all its inputs are loop invariants. Since loop invariant will immediately moved
// to dominator block of loop, the first rule actually already implies the second rule
func (s *state) tryHoist(val *Value) bool {
	s.hoisted[val] = false
	// arguments of val are all loop invariant, but they are not necessarily
	// hoistable due to various constraints, for example, memory alias, so
	// we try to hoist its arguments first
	for _, arg := range val.Args {
		if _, exist := s.invariants[arg]; !exist {
			// must be type of memory or defiend outside loop
			if !arg.Type.IsMemory() && !s.loopnest.sdom.IsAncestorEq(arg.Block, s.loop.header) {
				fmt.Printf("must define outside loop %v\n", arg.LongString())
				panic("must define outside loop")
			}
			continue
		} else {
			hoisted, visited := s.hoisted[arg]
			if !visited {
				if !s.tryHoist(arg) {
					return false
				}
			}
			if !hoisted {
				return false
			}
		}
	}

	// all arugments are hoisted, we can hoist val now
	if canSpeculativelyExecuteValue(val) {
		hoist(s.loopnest, s.loop, val)
		s.hoisted[val] = true
		return true
	}

	// Instructions are guaranteed to execute?
	if !s.isExecuteUnconditionally(val) {
		fmt.Printf("==not execute unconditional%v\n", val)
		return false
	}
	// Instructions access different memory locations?
	if !s.hasMemoryAlias(val) {
		fmt.Printf("==has mem alias%v\n", val)
		return false
	}
	fmt.Printf("==can not speculate%v\n", val.LongString())
	if !s.loopnest.f.rotateLoop(s.loop) {
		fmt.Printf("==can not rotate%v\n", s.loop.FullString())
		return false
	}

	fmt.Printf("==hoist2\n")
	hoist(s.loopnest, s.loop, val)
	s.hoisted[val] = true
	return true
}

// licm stands for loop invariant code motion, it hoists expressions that computes
// the same value while has no effect outside loop
func licm(f *Func) {
	// if f.Name != "(*itabTableType).find" {
	// 	return
	// }
	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}
	for _, loop := range loopnest.loops {
		loopBlocks := loopnest.findLoopBlocks(loop)
		// if len(loopBlocks) >= MaxLoopBlockSize {
		// 	continue
		// }

		// try to hoist loop invariant outside the loop
		loopnest.assembleChildren() // initialize loop children
		loopnest.findExits()        // initialize loop exits
		s := &state{loopnest: loopnest, loop: loop}
		invariants := s.markInvariant(loopBlocks)
		// TODO: invariants is unordered
		if invariants != nil && len(invariants) > 0 {
			fmt.Printf("==invariants %v\n", invariants)
			s.invariants = invariants
			s.hoisted = make(map[*Value]bool)

			sortedInvariants := make([]*Value, 0)
			for k, _ := range invariants {
				sortedInvariants = append(sortedInvariants, k)
			}
			sort.SliceStable(sortedInvariants, func(i, j int) bool {
				return sortedInvariants[i].ID < sortedInvariants[j].ID
			})

			for _, invariant := range sortedInvariants {
				s.tryHoist(invariant)
			}
		}
		// ok := f.rotateLoop(loop)
		// if ok {
		// 	//fmt.Printf("success: %s \n", f.Name)
		// } else {
		// 	//fmt.Printf("bad: %s \n", f.Name)
		// }
	}
}
