// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "fmt"

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

func printInvariant(val *Value, block *Block, domBlock *Block) {
	fmt.Printf("== Hoist %v(%v) from b%v to b%v in %v\n",
		val.Op.String(), val.String(),
		block.ID, domBlock.ID, block.Func.Name)
	fmt.Printf("  %v\n", val.LongString())
}

// isCandidate carefully selects a subset of values that allow them to be hoisted
// or sunk, as empirical evidence shows that not all loop invariants are worth
// applying LICM. Applying LICM to low-benefit values may increase register pressure
// on the loop header/exit blocks, which can have a negative impact on performance.
func isCandidate(val *Value) bool {
	switch val.Op {
	case OpLoad:
		return true
		// TODO: ADD STORE
	}
	return false
}

func isLoopInvariant(value *Value, invariants map[*Value]*Block,
	loopBlocks []*Block) bool {
	return true
}

// For Load/Store and some special Values they sould be processed separately
// even if they are loop invariants as they may have observable memory side
// effect
func canHoist(loads []*Value, stores []*Value, val *Value) bool {
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
			// fmt.Printf("%v == %v %v\n", at, loadPtr.LongString(), storePtr.LongString())
			if at != NoAlias {
				return false
			}
		}
		return true
	} else if val.Op == OpStore {
		if len(loads) == 0 {
			return true
		}
	}
	return false
}

func hoist(loopnest *loopnest, loop *loop, block *Block, val *Value) {
	for valIdx, v := range block.Values {
		if val != v {
			continue
		}
		domBlock := loopnest.sdom.Parent(loop.header)
		// if block.Func.pass.debug >= 1 {
		printInvariant(val, block, domBlock)
		// }
		val.moveTo(domBlock, valIdx)
		break
	}
}

// tryHoist hoists profitable loop invariant to block that dominates the entire loop.
// Value is considered as loop invariant if all its inputs are defined outside the loop
// or all its inputs are loop invariants. Since loop invariant will immediately moved
// to dominator block of loop, the first rule actually already implies the second rule
func tryHoist(loopnest *loopnest, loop *loop, loads []*Value, stores []*Value, invariants map[*Value]*Block) {
	for val, _ := range invariants {
		if !canHoist(loads, stores, val) {
			continue
		}
		// TODO: ADD LOOP GUARD
		//
		// func foo(arr[]int cnt int) {
		// 	r:=0
		// 	for i=0;i<cnt;i++{
		// 		r += arr[3]
		// 	}
		// 	return r
		// }
		//
		// we can not hoist arr[3] to loop header even if it' an invariant
		// because (Load arr,3) has observable side effect and may cause null
		// pointer error, we need to make sure loop must execute at least
		// once before hoistingn any Loads
		//
		// hoist(loopnest, loop, block, val)
		// TODO: FOR STORE VALUES, THEY SHOULD SINK
	}
}

func markInvariant(loopnest *loopnest, loop *loop, loopBlocks []*Block) {
	tooComplicated := false
	loopValues := make(map[*Value]bool)
	invariants := make(map[*Value]*Block)
	loads := make([]*Value, 0)
	stores := make([]*Value, 0)
	// First, collect all def inside loop
	for _, block := range loopBlocks {
		for _, val := range block.Values {
			loopValues[val] = true
		}
	}
Bailout:
	for _, block := range loopBlocks {
		// If basic block is located in a nested loop rather than directly in the
		// current loop, it will not be processed.
		if loopnest.b2l[block.ID] != loop {
			continue
		}

		for _, value := range block.Values {
			if value.Op == OpLoad {
				loads = append(loads, value)
			} else if value.Op == OpStore {
				stores = append(stores, value)
			} else if value.Op.IsCall() {
				tooComplicated = true
				break Bailout
			}
			// Store/Load depends on memory value, which is usually represented
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
			uses := value.Args
			if value.Op == OpStore || value.Op == OpLoad {
				// discard last memory value
				uses = uses[:len(uses)-1]
			}

			isInvariant := true
			for _, use := range uses {
				if _, t := invariants[use]; t {
					continue
				}
				if _, t := loopValues[use]; t {
					isInvariant = false
					break
				}
			}
			if isInvariant {
				invariants[value] = block
			}
		}
	}

	// bail out the compilation if too complicated, for example, loop involves Calls
	// Theoretically we can hoist Call as long as it does not impose any observable
	// side effects, e.g. only reads memory or dont access memory at all, but
	// unfortunate we may run alias analysis in advance to get such facts, that
	// some what heavy for this pass at present, so we give up further motion
	// once loop blocks involve Calls
	if !tooComplicated {
		tryHoist(loopnest, loop, loads, stores, invariants)
	}
}

// licm stands for loop invariant code motion, it hoists expressions that computes
// the same value while has no effect outside loop
func licm(f *Func) {
	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}
	for _, loop := range loopnest.loops {
		loopBlocks := loopnest.findLoopBlocks(loop)
		if len(loopBlocks) >= MaxLoopBlockSize {
			continue
		}

		// try to hoist loop invariant outside the loop
		loopnest.assembleChildren()
		markInvariant(loopnest, loop, loopBlocks)
	}
}
