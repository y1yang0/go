// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"sort"
)

// ----------------------------------------------------------------------------
// Loop Close SSA Form
//
// Loop close SSA form is a special form of SSA form, which is used to simplify
// loop optimization. The idea is to insert "close" phi at loop exits to make sure
// all uses of a loop defined value are dominated by the loop close phi.
//
//	 loop header:                         loop header:
//	 v3 = Phi [0], v4                     v3 = Phi [0], v4
//	 If cond->loop latch,loop exit        If cond->loop latch,loop exit
//
//	 loop latch:                          loop latch:
//	 v4 = Add v3, [1]               =>    v4 = Add v3, [1]
//	 Plain->loop header                   Plain->loop header
//
//	 loop exit:                           loop exit:
//	 v5 = Add64 5, v3                     v6 = Phi(v3)  <= Loop-close Phi
//	 Ret v18                              v5 = Add64 5, v6
//                                        Ret v18
//
//
// Any changes to the loop defined value will be reflected in the loop close phi
// instead of iterating through all uses of the loop defined value and update them
// carefully with respect to dominance relationship, which is error prone and
// hard to maintain.

const LoopClosePhiAux string = ".lcphi"

type loopUse struct {
	val   *Value // user is Value
	block *Block // user is block's ctrl Value
}

type loopDefUses map[*Value][]*loopUse

func (lu *loopUse) String() string {
	return fmt.Sprintf("{%v,%v}", lu.val, lu.block)
}

func (lu *loopUse) useBlock(def *Value) *Block {
	var ub *Block
	if val := lu.val; val != nil {
		if val.Op == OpPhi {
			// Used by Phi? Use corresponding incoming block as the real use
			// block, because loop def does not really dominate Phi
			for ipred, pred := range val.Args {
				if pred == def {
					ub = val.Block.Preds[ipred].b
					break
				}
			}
		} else {
			ub = val.Block
		}
	} else {
		ub = lu.block
	}
	assert(ub != nil, "no use block")
	return ub
}

func (lu *loopUse) replaceUse(def *Value, newUse *Value) {
	if val := lu.val; val != nil {
		i := -1
		for idx, arg := range val.Args {
			if arg == def {
				i = idx
				break
			}
		}
		if i != -1 {
			val.SetArg(i, newUse)
		} else {
			panic("not a valid use")
		}
	} else if block := lu.block; block != nil {
		for idx, ctrl := range block.ControlValues() {
			if ctrl == def {
				block.ReplaceControl(idx, newUse)
				break
			}
		}
	} else {
		panic("loop def is neither used by value nor by block")
	}
}

func containsBlock(ln *loopnest, loop *loop, block *Block) bool {
	if ln.b2l[block.ID] == loop {
		return true
	}
	for _, child := range loop.children {
		if ln.b2l[block.ID] == child {
			return true
		}
	}
	return false
}

func isLoopClosePhi(val *Value) bool {
	if val.Op == OpPhi && val.Aux != nil && auxToString(val.Aux) == LoopClosePhiAux {
		return true
	}
	return false
}

func newLoopClosePhi(fn *Func, exit *Block, loopDef *Value) *Value {
	phi := fn.newValueNoBlock(OpPhi, loopDef.Type, loopDef.Pos)
	phi.Aux = StringToAux(LoopClosePhiAux) // indicate this is a loop close phi
	phiArgs := make([]*Value, len(exit.Preds))
	for idx := range exit.Preds {
		phiArgs[idx] = loopDef
	}
	phi.AddArgs(phiArgs...)
	exit.placeValue(phi)
	return phi
}

func (fn *Func) placeLoopClosePhi(ln *loopnest, loop *loop, defUses loopDefUses) bool {
	sdom := fn.Sdom()
	keys := make([]*Value, 0)
	for k, _ := range defUses {
		keys = append(keys, k)
	}
	sort.SliceStable(keys, func(i, j int) bool {
		return keys[i].ID < keys[j].ID
	})
	for _, loopDef := range keys {
		// multiple uses shares the same close phi if they live in same exit block
		e2phi := make(map[*Block]*Value, 0)
		for _, use := range defUses[loopDef] {
			useBlock := use.useBlock(loopDef)

			if ln.b2l[useBlock.ID] == loop {
				continue
			}

			// Only loop use that located in current loop takes into account
			if useBlock != loopDef.Block && !containsBlock(ln, loop, useBlock) {
				// Find a proper block to place loop close phi
				var foundExit *Block
				for _, exit := range loop.exits {
					if sdom.IsAncestorEq(exit, useBlock) {
						foundExit = exit
						break
					}
				}
				if foundExit == nil {
					// TODO: REVIVE THIS
					// cnt := 0
					// for _, pred := range useBlock.Preds {
					// 	for _, e := range loop.exits {
					// 		if e == pred.b {
					// 			cnt++
					// 			break
					// 		}
					// 	}
					// }
					// if cnt != len(useBlock.Preds) {
					// 	fmt.Printf("==BAD\n")
					// } else {
					// 	fmt.Printf("==GOOD1\n")
					// }
					return false
				} else {
					// fmt.Printf("==GOOD\n")
				}

				// Allocate close phi in that block
				var phi *Value
				if phival, exist := e2phi[foundExit]; exist {
					phi = phival
				} else {
					phi = newLoopClosePhi(fn, foundExit, loopDef)
					e2phi[foundExit] = phi
				}

				// Replace all uses of loop def with new close phi
				if fn.pass.debug > 1 {
					fmt.Printf("Replace loop use %v with loop close %v\n", use, phi)
				}
				use.replaceUse(loopDef, phi)
			}
		}
	}
	return true
}

// BuildLoopCloseForm builds Loop Close SSA Form upon original loop form, this is
// the cornerstone of other loop optimizations such as LICM and loop unswitching
//
// 5439/64298 good/bad build
func (fn *Func) BuildLoopCloseForm(ln *loopnest, loop *loop) bool {
	if len(loop.exits) == 0 {
		return true
	}

	// Outside the loop we can only use values defined in the blocks of arbitrary
	// loop exit dominators, so first collect these blocks and treat the Values
	// in them as loop def
	domBlocks := make([]*Block, 0)
	blocks := make([]*Block, 0)
	blocks = append(blocks, loop.exits...)

	for len(blocks) > 0 {
		block := blocks[0]
		blocks = blocks[1:]
		if block == loop.header {
			continue
		}
		idom := ln.sdom.Parent(block)
		if ln.b2l[idom.ID] != loop {
			continue
		}

		domBlocks = append(domBlocks, idom)
		blocks = append(blocks, idom)
	}

	// Look for out-of-loop users of these loop defs
	defUses := make(loopDefUses, 0)
	for _, block := range domBlocks {
		for _, val := range block.Values {
			if val.Uses == 0 {
				continue
			}
			if _, exist := defUses[val]; !exist {
				// many duplicate definitions, avoid redundant mem allocations
				defUses[val] = make([]*loopUse, 0, val.Uses)
			}
		}
	}
	for _, block := range fn.Blocks {
		for _, val := range block.Values {
			for _, arg := range val.Args {
				if _, exist := defUses[arg]; exist {
					defUses[arg] = append(defUses[arg], &loopUse{val, nil})
				}
			}
		}
		for _, ctrl := range block.ControlValues() {
			if _, exist := defUses[ctrl]; exist {
				defUses[ctrl] = append(defUses[ctrl], &loopUse{nil, block})
			}
		}
	}

	// Finally, insert loop close Phis at the closest loop exits of the blocks
	// where loop uses are located, and then instead of using the loop def
	// directly, the uses use these newly inserted loop close phi
	return fn.placeLoopClosePhi(ln, loop, defUses)
	// TODO: VERIFY FORM
}
