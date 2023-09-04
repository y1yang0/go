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
// In the context of LICM, we can classify all Values into two categories: those
// that can undergo speculative execution and those that cannot. Examples of the
// former include simple arithmetic operations (except for division and modulo
// which may trap execution due to / by zero), which can be freely hoisted to the
// loop entry. However, for the latter category, there are several prerequisites.
// To ensure program semantic correctness, Values must satisfy the following
// conditions in order to hoist it:
// TODO: TO WRITE

const MaxLoopBlockSize = 8

type state struct {
	fn *Func
	loopnest   *loopnest // the global loopnest
	loop       *loop     // target loop to be optimized out
	loads      []*Value
	stores     []*Value
	invariants map[*Value]bool
	hoisted    map[*Value]bool
}

func printInvariant(val *Value, block *Block, domBlock *Block) {
	fmt.Printf("== Hoist %v from b%v to b%v in %v\n",
		val.String(),
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
			return false
		}
		// Slow path, we need a type-based alias analysis to know whether Load
		// may alias with Stores
		for _, st := range stores {
			loadPtr := val.Args[0]
			storePtr := st.Args[0]
			at := GetMemoryAlias(loadPtr, storePtr)
			fmt.Printf("==%v %v with %v in %v\n", at, loadPtr.LongString(), storePtr.LongString(), val.Block.Func.Name)
			if at != NoAlias {
				return true
			}
		}
		return false
	} else if val.Op == OpStore {
		if len(loads) == 0 && len(stores) == 1 /*itself only*/ {
			return false
		}
		for _, v := range append(stores, loads...) {
			ptr := v.Args[0]
			storePtr := val.Args[0]
			at := GetMemoryAlias(ptr, storePtr)
			fmt.Printf("==%v %v with %v in %v\n", at, ptr.LongString(), storePtr.LongString(), val.Block.Func.Name)
			if at != NoAlias {
				return true
			}
		}
		return false
	} else {
	//	fmt.Printf("==TO IMPLEMENT:%v\n", val.LongString())
	}
	return false
}

// isExecuteUnconditionally checks if Value is guaranteed to execute during loop iterations
// Otherwise, it should not be hoisted. The most common cases are invariants guarded by
// conditional expressions.
func (s *state) isExecuteUnconditionally(val *Value) bool {
	block := val.Block
	sdom := s.fn.Sdom()
	for _, exit := range s.loop.exits {
		if exit == s.loop.exit {
			if !sdom.IsAncestorEq(block, s.loop.latch) {
				return false
			}
			continue
		}
		if !sdom.IsAncestorEq(block, exit) {
			// fmt.Printf("==unc %v", exit.LongString())
			// pred := exit.Preds[0].b
			// if len(pred.ControlValues())>0 {
			// 	ct := pred.ControlValues()[0]
			// 	if s.invariants[ct] {
			// 		fmt.Printf("==inv %v", ct)
			// 	}
			// }
			return false
		}
	}
	return true
}

func (s *state) hoist(block *Block, val *Value) {
	// rewire memory Phi input if needed
	for idx, arg := range val.Args {
		if arg.Type.IsMemory() && arg.Op == OpPhi{
			for _, phiArg := range arg.Args {
				if s.fn.Sdom().IsAncestorEq(phiArg.Block, val.Block) {
					val.SetArg(idx, phiArg)
					break
				}
			}
		}
	}
	for valIdx, v := range val.Block.Values {
		if val != v {
			continue
		}
		s.hoisted[val] = true
		val.moveTo(block, valIdx)
		break
	}
}

func isHoistable(val*Value) bool{
	switch val.Op {
	case OpPhi,OpInlMark, OpVarDef, OpVarLive, OpInvalid:
		return false
	}
	return true
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
		if arg.Type.IsMemory() {
			continue
		}
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

	if !isHoistable(val) {
		fmt.Printf("==isnothoistable %v\n", val.LongString())
		return false
	}

	// Hoist value to loop entry
	if canSpeculativelyExecuteValue(val) {
		// If arguments of value is hoisted to loop land, the value itself should
		// be hoisted to loop land
		for _,arg := range val.Args {
			if s.loop.guard != nil && !s.fn.Sdom().IsAncestorEq(arg.Block, s.loop.guard) {
				s.hoist(s.loop.land, val)
				fmt.Printf("==Hoist1 %v to %v\n", val.LongString(), s.loop.land)
				return true
			}
		}
		entry := s.fn.Sdom().Parent(s.loop.header)
		s.hoist(entry, val)
		fmt.Printf("==Hoist1 %v to %v\n", val.LongString(), entry)
		return true
	}

	// Dont worry, we can hoist some Values even if they can not speculatively
	// execute, for example, Load, Store, etc, but requiring a few prerequisites

	// Instructions access different memory locations?
	if s.hasMemoryAlias(val) {
		fmt.Printf("==has mem alias%v\n", val)
		return false
	}

	// Instructions are located in rotatable loop?
	fmt.Printf("==can not speculate%v\n", val.LongString())
	if !s.loopnest.f.RotateLoop(s.loop) {
		fmt.Printf("==can not rotate%v\n", s.loop.LongString())
		return false
	}

	if val.Block.Kind == BlockIf {
		OOO:
		for _,succ:= range val.Block.Succs {
			for _, v:= range succ.b.Values {
				if v.Op == OpPanicBounds || v.Op == OpPanicExtend {
					fmt.Printf("+++PANIC")
					break OOO
				}
			}
		}
	}
	// First apply loop rotation and then rely on dominator tree
	// Instructions are guaranteed to execute after entering loop?
	if !s.isExecuteUnconditionally(val) {
		// Because loop header can always jump to the loop exit, all blocks
		// inside the loop are never post-dominated by any loop exit.
		// Therefore, we need to first apply loop rotation to eliminate the path
		// from the loop header to the loop exit.
		fmt.Printf("==not execute unconditional%v\n", val.LongString())
		return false
	}

	if !s.loop.CreateLoopLand(s.loopnest.f) {
		fmt.Printf("==can not create safe land")
		return false
	}

	// Hoist value to loop land
	s.hoist(s.loop.land, val)
	fmt.Printf("==Hoist2 %v to %v\n", val.LongString(), s.loop.land)
	return true
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
				if use.Type.IsMemory() && use.Op == OpPhi {
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
					//
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

// licm stands for loop invariant code motion, it hoists expressions that computes
// the same value while has no effect outside loop
func licm(f *Func) {
	// if f.Name != "partitionByArgClass.Less" {
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
		s := &state{loopnest: loopnest, loop: loop, fn:f}
		invariants := s.markInvariant(loopBlocks)

		if invariants != nil && len(invariants) > 0 {
			fmt.Printf("==invariants%v %v in %v\n", loop.header,invariants, f.Name)
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
		// ok := f.RotateLoop(loop)
		// if ok {
		// 	//fmt.Printf("success: %s \n", f.Name)
		// } else {
		// 	//fmt.Printf("bad: %s \n", f.Name)
		// }
	}
}
