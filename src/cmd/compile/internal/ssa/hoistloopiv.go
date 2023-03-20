// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "fmt"

const MaxLoopBlockSize = 8

func isCandidate(block *Block, val *Value) bool {
	if len(val.Args) == 0 {
		// not a profitable expression, e.g. constant
		return false
	}
	if block.Likely == BranchUnlikely {
		// all values are excluded as candidate when branch becomes unlikely to reach
		return false
	}
	return true
}

func isInsideLoop(loopnest *loopnest, loop *loop, val *Value) bool {
	if loopnest.b2l[val.Block.ID] == loop {
		return true
	}
	for _, child := range loop.children {
		if isInsideLoop(loopnest, child, val) {
			return true
		}
	}
	return false
}

// tryHoist hoists profitable loop invariant to block that dominates the entire loop.
// Value is considered as loop invariant if all its inputs are defined outside the loop
// or all its inputs are loop invariants. Since loop invariant will immediately moved
// to dominator block of loop, the first rule actually already implies the second rule
func tryHoist(loopnest *loopnest, loop *loop, loopBlocks []*Block) {
	for _, block := range loopBlocks {
		for i := 0; i < len(block.Values); i++ {
			var val *Value = block.Values[i]
			if !isCandidate(block, val) {
				continue
			}
			// value can hoist because it may causes observable side effects
			if hasSideEffect(val) {
				continue
			}
			// consider the following operation as pinned anyway
			switch val.Op {
			case OpInlMark,
				OpAtomicLoad8, OpAtomicLoad32, OpAtomicLoad64,
				OpAtomicLoadPtr, OpAtomicLoadAcq32, OpAtomicLoadAcq64:
				continue
			}
			// input def is inside loop, consider as variant
			isInvariant := true
			for _, arg := range val.Args {
				if isInsideLoop(loopnest, loop, arg) {
					isInvariant = false
					break
				}
			}
			if isInvariant {
				for valIdx, v := range block.Values {
					if val != v {
						continue
					}
					domBlock := loopnest.sdom.Parent(loop.header)
					fmt.Printf("== Hoist %v(%v) from b%v to b%v %v in %v %v\n",
						val.Op.String(), val.String(),
						val.Block.ID, domBlock.ID, loopnest.sdom.Parent(block), block.Func.Name, loopBlocks)
					for _, arg := range val.Args {
						fmt.Printf("=>%v %v ch%v\n", arg.LongString(), isInsideLoop(loopnest, loop, arg), len(loop.children))
					}
					val.moveTo(domBlock, valIdx)
					i--
					break
				}
			}
		}
	}
}

// hoistLoopInvariant hoists expressions that computes the same value
// while has no effect outside loop
func hoistLoopInvariant(f *Func) {
	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}
	for _, loop := range loopnest.loops {
		loopBlocks := make([]*Block, 0)
		loopBlocks = append(loopBlocks, loop.header)
		tooComplicated := false
		// collect loop blocks by walking backedge
		for i := 0; i < len(loopBlocks); i++ {
			var block = loopBlocks[i]
			for _, pred := range block.Preds {
				predBlock := pred.b
				if predBlock.Kind != BlockPlain {
					continue
				}

				if loopnest.b2l[predBlock.ID] != loop {
					continue
				}
				if predBlock == nil || predBlock == block {
					continue
				}
				found := false
				for _, t := range loopBlocks {
					if t == predBlock {
						found = true
						break
					}
				}
				if !found {
					loopBlocks = append(loopBlocks, predBlock)
					// if len(loopBlocks) >= MaxLoopBlockSize {
					// 	tooComplicated = true
					// 	break
					// }
				}
			}
		}
		// check if it's too complicated for such optmization
		for _, block := range loopBlocks {
			for _, val := range block.Values {
				if val.Op.IsCall() || val.Op.HasSideEffects() {
					tooComplicated = true
					break
				}
				switch val.Op {
				case OpLoad, OpStore:
					tooComplicated = true
					break
				}
			}
		}
		// try to hoist loop invariant outside the loop
		if !tooComplicated {
			tryHoist(loopnest, loop, loopBlocks)
		}
	}
}
