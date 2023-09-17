// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

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
	if val.Op == OpPhi && auxToString(val.Aux) == LoopClosePhiAux {
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
	//fmt.Printf("==newphi%v %v\n", phi.LongString(), exit)
	exit.placeValue(phi)
	return phi
}

func (fn *Func) placeLoopClosePhi(ln *loopnest, loop *loop, loopDefs []*Value) bool {
	// build def use chains
	defUses := make(map[*Value][]interface{})
	for _, loopDef := range loopDefs {
		if loopDef.Uses > 0 {
			defUses[loopDef] = make([]interface{}, 0, loopDef.Uses)
		}
	}
	for _, block := range fn.Blocks {
		for _, val := range block.Values {
			for _, arg := range val.Args {
				if _, exist := defUses[arg]; exist {
					defUses[arg] = append(defUses[arg], val)
				}
			}
		}
		for _, ctrl := range block.ControlValues() {
			if _, exist := defUses[ctrl]; exist {
				defUses[ctrl] = append(defUses[ctrl], block)
			}
		}
	}

	// For every loop defs, check if we need to insert loop close phi

	getUseBlock := func(use interface{}, loopDef *Value) *Block {
		var useBlock *Block
		switch use := use.(type) {
		case *Value:
			if use.Op == OpPhi {
				// Used by Phi? Use corresponding incoming block as the real use
				// block, because arguments of Phi dont dominate Phi itself
				for ipred, pred := range use.Args {
					if pred == loopDef {
						useBlock = use.Block.Preds[ipred].b
						break
					}
				}
			} else {
				useBlock = use.Block
			}
		case *Block:
			useBlock = use
		default:
			panic("should not reach here")
		}
		return useBlock
	}
	sdom := fn.Sdom()
	for len(loopDefs) > 0 {
		loopDef := loopDefs[0]
		loopDefs = loopDefs[1:]

		if len(loop.exits) == 0 {
			continue
		}

		// Collect all uses of loop def that live outside loop
		uses := make([]interface{}, 0)
		for _, use := range defUses[loopDef] {
			useBlock := getUseBlock(use, loopDef)
			if useBlock == nil {
				continue
			}
			if ln.b2l[useBlock.ID] == loop {
				continue
			}
			if useBlock != loopDef.Block && !containsBlock(ln, loop, useBlock) {
				uses = append(uses, use)
			}
		}
		if len(uses) == 0 {
			continue
		}

		// fmt.Printf("==DEF%v USES%v %v\n", loopDef.LongString(), uses, loop.exits)
		b2phi := make(map[*Block]*Value, 0)
		for _, use := range uses {
			useBlock := getUseBlock(use, loopDef)
			var foundExit *Block
			for _, exit := range loop.exits {
				if sdom.IsAncestorEq(exit, useBlock) {
					foundExit = exit
					break
				}
			}
			if foundExit == nil {
				// TODO: REVIVE THIS
				// for _, pred := range useBlock.Preds {
				// 	second := false
				// 	for _, e := range loop.exits {
				// 		if e == pred.b {
				// 			second = true
				// 			break
				// 		}
				// 	}
				// 	if second == false {
				// 		//fmt.Printf("==BAD\n")
				// 	}
				// 	break
				// }
				return false
			} else {
				// //fmt.Printf("GOOD\n")
			}
			switch use := use.(type) {
			case *Block:
				for idx, ctrl := range use.ControlValues() {
					if ctrl == loopDef {
						var phi *Value
						if phival, exist := b2phi[foundExit]; exist {
							phi = phival
						} else {
							phi = newLoopClosePhi(fn, foundExit, loopDef)
							b2phi[foundExit] = phi
						}
						useBlock.ReplaceControl(idx, phi)
						// fmt.Printf("==lcssa ctrl old %v new %v\n",
						// 	use.LongString(), phi.LongString())
						break
					}
				}
			case *Value:
				for idx, arg := range use.Args {
					if arg == loopDef {
						var phi *Value
						if phival, exist := b2phi[foundExit]; exist {
							phi = phival
						} else {
							phi = newLoopClosePhi(fn, foundExit, loopDef)
							b2phi[foundExit] = phi
						}
						use.SetArg(idx, phi)
						// fmt.Printf("==lcssa old %v new %v\n",
						// 	use.LongString(), phi.LongString())
						break
					}
				}
			}
		}

	}
	return true
}

// BuildLoopCloseForm tries to transform original loop to Loop Close SSA Form, it
// is the cornerstone of other loop optimizations such as LICM and loop unswitching
func (fn *Func) BuildLoopCloseForm(ln *loopnest, loop *loop) bool {
	if len(loop.exits) == 0 {
		return true
	}

	// If a block dominates any one of loop exits, Values defined in such block
	// are able to be used outside loop
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

	// Find Values that defined in previous blocks and used outside lopp
	loopDefs := make([]*Value, 0)
	for _, block := range domBlocks {
		for _, val := range block.Values {
			if val.Uses == 0 {
				continue
			}
			loopDefs = append(loopDefs, val)
		}
	}
	//fmt.Printf("==LCSSA Form %v %v\n", loop.header, loop.exits)
	// Insert proper loop close phi for these uses
	return fn.placeLoopClosePhi(ln, loop, loopDefs)
	// TODO: VERIFY FORM
}
