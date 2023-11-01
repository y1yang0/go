// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"sort"
)

// ----------------------------------------------------------------------------
// Loop Closed SSA Form
//
// loop closed SSA form is a special form of SSA form, which is used to simplify
// loop optimization. It ensures that all values defined inside the loop are only
// used within loop. The transformatio looks up loop use outside the loop and
// inserts the appropriate "proxy phi" at the loop exit, after which the outside
// of the loop does not use the loop def directly but the proxy phi.
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
//	 v5 = Add64 5, v3                     v6 = Phi(v3)  <= Proxy Phi
//	 Ret v18                              v5 = Add64 5, v6
//	                                      Ret v18
//
//
// Any changes to the loop defined value will be reflected in the proxy phi
// instead of iterating through all uses of the loop defined value and update
// them carefully with respect to dominance relationship, which is error prone
// and hard to maintain.

// Def-Use utilities
type user struct {
	def   *Value // the definition
	val   *Value // user is Value
	block *Block // user is block's ctrl Value
}

type defUses map[*Value][]*user

func (u *user) String() string {
	if u.val != nil {
		return fmt.Sprintf("{%v:%v}", u.def, u.val)
	} else {
		return fmt.Sprintf("{%v:%v}", u.def, u.block)
	}
}

// useBlock returns the block where the def is used
func (u *user) useBlock() *Block {
	if u.val != nil {
		return u.val.Block
	} else {
		return u.block
	}
}

// replaceUse replaces the use of def with new use
func (u *user) replaceUse(newUse *Value) {
	if val := u.val; val != nil {
		i := -1
		for idx, arg := range val.Args {
			if arg == u.def {
				i = idx
				break
			}
		}
		if i != -1 {
			val.SetArg(i, newUse)
		} else {
			panic("not a valid use")
		}
	} else if block := u.block; block != nil {
		for idx, ctrl := range block.ControlValues() {
			if ctrl == u.def {
				block.ReplaceControl(idx, newUse)
				break
			}
		}
	} else {
		panic("loop def is neither used by value nor by block")
	}
}

// buildDefUses builds def-use map for given defs Values
func buildDefUses(fn *Func, defs []*Value) defUses {
	// TODO: Could we maintain def-use across whole compilation instead of in-place
	// creation as it is widely used?
	defUses := make(defUses, 0)
	for _, def := range defs {
		if _, exist := defUses[def]; !exist {
			// Many duplicate definitions, avoid redundant mem allocations
			defUses[def] = make([]*user, 0, def.Uses)
		}
	}
	for _, block := range fn.Blocks {
		for _, val := range block.Values {
			for _, arg := range val.Args {
				if _, exist := defUses[arg]; exist {
					defUses[arg] = append(defUses[arg], &user{arg, val, nil})
				}
			}
		}
		for _, ctrl := range block.ControlValues() {
			if _, exist := defUses[ctrl]; exist {
				defUses[ctrl] = append(defUses[ctrl], &user{ctrl, nil, block})
			}
		}
	}
	return defUses
}

type lcssa struct {
	fn    *Func
	mphis []*Value          // memory proxy phi
	e2phi map[*Block]*Value // exit block to proxy phi mapping
}

// findUseBlock returns the block where the def is used. If the use is type of Phi,
// then the use block is the corresponding incoming block. Note that this is ONLY
// valid in context of LCSSA.
func findUseBlock(u *user) *Block {
	var ub *Block
	if val := u.val; val != nil {
		if val.Op == OpPhi {
			for ipred, pred := range val.Args {
				if pred == u.def {
					ub = val.Block.Preds[ipred].b
					break
				}
			}
		} else {
			ub = val.Block
		}
	} else {
		ub = u.block
	}
	assert(ub != nil, "no use block")
	return ub
}

// containsBlock returns true if the block is part of the loop or part of the inner
// loop
func (ln *loopnest) containsBlock(loop *loop, block *Block) bool {
	// Block is part of current loop?
	if ln.b2l[block.ID] == loop {
		return true
	}
	// Block is part of inner loop?
	for _, child := range loop.children {
		if ln.containsBlock(child, block) {
			return true
		}
	}
	return false
}

// allocateProxyPhi allocates a proxy phi at specific loop exit
func (lc *lcssa) allocateProxyPhi(exit *Block, loopDef ...*Value) *Value {
	assert(len(loopDef) > 0, "must have at least one loop def")
	if phival, exist := lc.e2phi[exit]; exist {
		return phival
	}

	phi := lc.fn.newValueNoBlock(OpPhi, loopDef[0].Type, loopDef[0].Pos)
	if len(loopDef) == 1 {
		phiArgs := make([]*Value, len(exit.Preds))
		for idx := range exit.Preds {
			phiArgs[idx] = loopDef[0]
		}
		phi.AddArgs(phiArgs...)
	} else {
		phi.AddArgs(loopDef...)
	}

	exit.placeValue(phi)
	lc.e2phi[exit] = phi
	if phi.Type.IsMemory() {
		lc.mphis = append(lc.mphis, phi)
	}
	return phi
}

func (lc *lcssa) fixProxyPhiMem(fn *Func) {
	lastMem := computeLastMem(fn)
	for _, phi := range lc.mphis {
		if !phi.Type.IsMemory() {
			continue
		}
		for iarg, arg := range phi.Args {
			mem := lastMem[phi.Block.Preds[iarg].b.ID]
			if mem != arg && mem != nil {
				assert(mem.Args[0] == arg, "must use old memory")
				phi.SetArg(iarg, mem)
			}
		}
	}
}

// placeProxyPhi places the proxy phi at loop exits to make sure all uses of a
// loop defined value are dominated by the proxy phi
func (lc *lcssa) placeProxyPhi(ln *loopnest, loop *loop, defs []*Value) bool {
	defUses := buildDefUses(ln.f, defs)

	// Make it deterministic to avoid compilation stale
	keys := make([]*Value, 0)
	for k := range defUses {
		keys = append(keys, k)
	}
	sort.SliceStable(keys, func(i, j int) bool {
		return keys[i].ID < keys[j].ID
	})

	lc.mphis = make([]*Value, 0, len(keys))
	// For every loop def, find its uses outside the loop
	for _, loopDef := range keys {
		// multiple uses shares the same proxy phi if they live in same exit block
		// also note that only users of the same loop def could share proxy phi
		lc.e2phi = make(map[*Block]*Value, 0)

		// For every use of loop def, place the proxy phi at proper exit block
		// and replace such use with the proxy phi, this is the core of LCSSA,
		// since proxy phi is "inside the loop" in context of LCSSA, now all uses
		// of loop def are loop closed, e.g. lives in the loop.
		for _, use := range defUses[loopDef] {
			useBlock := findUseBlock(use)
			// Use is part of current loop? Skip it
			if ln.b2l[useBlock.ID] == loop {
				continue
			}

			// Loop def does not dominate use? Possibly dead block, skip it
			if !ln.sdom.IsAncestorEq(loopDef.Block, useBlock) {
				continue
			}

			// Only loop use that is not part of current loop takes into account.
			if useBlock != loopDef.Block && !ln.containsBlock(loop, useBlock) {
				// First, try to find a loop exit that dominates the use block
				// and place the proxy phi at this loop exit, this is the most
				// common case
				var domExit *Block
				for _, exit := range loop.exits {
					if ln.sdom.IsAncestorEq(exit, useBlock) {
						domExit = exit
						break
					}
				}
				if domExit != nil {
					// Replace all uses of loop def with new close phi
					lcphi := lc.allocateProxyPhi(domExit, loopDef)
					use.replaceUse(lcphi)
					// if ln.f.pass.debug > 1 {
					fmt.Printf("== Replace use %v with proxy phi %v\n",
						use, lcphi.LongString())
					// }
					continue
				}

				// Harder case, loop use block is not dominated by a single loop
				// exit, instead it has many predecessors and all of them are
				// dominated by different loop exits, we are probably reaching to
				// it from all of these predecessors. In this case, we need to
				// place the proxy phi at all loop exits and merge them at loop
				// use block by yet another proxy phi
				if len(useBlock.Preds) == 0 {
					assert(useBlock.Kind == BlockInvalid, "why not otherwise")
					continue
				}
				domExits := make([]*Block, 0, len(useBlock.Preds))
				for _, pred := range useBlock.Preds {
					for _, e := range loop.exits {
						if ln.sdom.IsAncestorEq(e, pred.b) {
							domExits = append(domExits, e)
							break
						}
					}
				}
				if cap(domExits) == len(domExits) {
					// Place loop closed phi at all dominator loop exits
					phis := make([]*Value, 0, len(domExits))
					for _, exit := range domExits {
						lcphi := lc.allocateProxyPhi(exit, loopDef)
						phis = append(phis, lcphi)
					}
					// Merge them at loop use block by yet another loop closed phi
					lcphi := lc.allocateProxyPhi(useBlock, phis...)
					use.replaceUse(lcphi)
					// if ln.f.pass.debug > 1 {
					fmt.Printf("== Replace use %v with proxy phi %v\n",
						use, lcphi.LongString())
					// }
					continue
				}

				// Worst case, loop use block is not dominated by any of loop exits
				// we start from all loop exits(including inner loop exits) though
				// dominance frontier and see if we can reach to the use block,
				// if so, we place the proxy phi at the loop exit that is closest
				// to the use block.
				// TODO: This is rare, but it does happen, give up for now as it's
				// hard to handle.
				if ln.f.pass.debug > 1 {
					fmt.Printf("== Can not process use %v, give up\n", use)
				}
				return false
			}
		}
	}

	// Since we may have placed memory proxy phi at some loop exits, which
	// use loop def and produce new memory. If this block is a predecessor
	// of another loop exit, we need to use memory proxy phi instead of loop
	// def as a parameter of new proxy phi.
	lc.fixProxyPhiMem(ln.f)
	return true
}

// BuildLoopClosedForm builds loop closed SSA Form upon original loop form, this is
// the cornerstone of other loop optimizations such as LICM and loop unswitching
func (fn *Func) BuildLoopClosedForm(ln *loopnest, loop *loop) bool {
	if len(loop.exits) == 0 {
		return true
	}

	sdom := ln.sdom // lcssa does not wire up CFG, reusing sdom is okay
	domBlocks := make([]*Block, 0)
	blocks := make([]*Block, 0)
	blocks = append(blocks, loop.exits...)

	// Outside the loop we can only use values defined in the blocks of arbitrary
	// loop exit dominators, so first collect these blocks and treat the Values
	// in them as loop def
	for len(blocks) > 0 {
		block := blocks[0]
		blocks = blocks[1:]
		if block == loop.header {
			continue
		}
		idom := sdom.Parent(block)
		if ln.b2l[idom.ID] != loop {
			continue
		}

		domBlocks = append(domBlocks, idom)
		blocks = append(blocks, idom)
	}

	// Look for out-of-loop users of these loop defs
	defs := make([]*Value, 0)
	for _, block := range domBlocks {
		for _, val := range block.Values {
			if val.Uses == 0 {
				continue
			}
			defs = append(defs, val)
		}
	}
	// For every use of loop def, place the proxy phi at the proper block
	lc := &lcssa{fn, nil, nil}
	return lc.placeProxyPhi(ln, loop, defs)
}
