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

func isLoopInvariant(theValue *Value, invariants map[*Value]*Block,
	loopBlocks []*Block) bool {
	for _, arg := range theValue.Args {
		if _, t := invariants[arg]; t {
			continue
		}

		// if uses are within loop, this is not an invariant as well
		for _, block := range loopBlocks {
			for _, val := range block.Values {
				if val == theValue {
					return false
				}
			}
		}
	}
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
		// no other Store accesses same type of memory
		sameType := false
		for st := range stores {
			if st.Type == val.Type {
				sameType = true
				break
			}
		}
		if !sameType {
			return true
		}
		// otherwise, we know nothing about memory alias, assume worst
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
		if block.Func.pass.debug >= 1 {
			printInvariant(val, block, domBlock)
		}
		val.moveTo(domBlock, valIdx)
		break
	}
}

// tryHoist hoists profitable loop invariant to block that dominates the entire loop.
// Value is considered as loop invariant if all its inputs are defined outside the loop
// or all its inputs are loop invariants. Since loop invariant will immediately moved
// to dominator block of loop, the first rule actually already implies the second rule
func tryHoist(loopnest *loopnest, loop *loop, loopBlocks []*Block) {
	invariants := make(map[*Value]*Block)
	loads := make([]*Value, 0)
	stores := make([]*Value, 0)

	for _, block := range loopBlocks {
		// if basic block is located in a nested loop rather than directly in the
		// current loop, it will not be processed.
		if loopnest.b2l[block.ID] != loop {
			continue
		}
		for i := 0; i < len(block.Values); i++ {
			var val *Value = block.Values[i]
			if !isCandidate(val) {
				continue
			}

			loopnest.assembleChildren()
			isInvariant := isLoopInvariant(val, invariants, loopBlocks)

			if isInvariant {
				invariants[val] = block
				if val.Op == OpLoad {
					loads = append(loads, val)
				} else if val.Op == OpStore {
					stores = append(stores, val)
				}
			}
		}
	}

	for val, block := range invariants {
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
		hoist(loopnest, loop, block, val)
		// TODO: FOR STORE VALUES, THEY SHOULD SINK
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

		// Theoretically we can hoist Call as long as it does not impose any observable
		// side effects, e.g. only reads memory or dont access memory at all, but
		// unfortunate we may run alias analysis in advance to get such facts, that
		// some what heavy for this pass at present, so we give up further motion
		// once loop blocks involve Calls
		tooComplicated := false
	Out:
		for _, block := range loopBlocks {
			for _, val := range block.Values {
				if val.Op.IsCall() || val.Op.HasSideEffects() {
					tooComplicated = true
					break Out
				}
			}
		}
		// try to hoist loop invariant outside the loop
		if !tooComplicated {
			tryHoist(loopnest, loop, loopBlocks)
		}
	}
}
