// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"sort"
)

// ----------------------------------------------------------------------------
// Loop Rotation
//
// Loop rotation transforms while/for loop to do-while style loop. The original
// natural loop is in form of below shape
//
//	   entry
//	     │
//	     │
//	     │  ┌───loop latch
//	     ▼  ▼       ▲
//	loop header     │
//	     │  │       │
//	     │  └──►loop body
//	     │
//	     ▼
//	 loop exit
//
// In the terminology, loop entry dominates the entire loop, loop header contains
// the loop conditional test, loop body refers to the code that is repeated, loop
// latch contains the backedge to loop header, for simple loops, the loop body is
// equal to loop latch, and loop exit refers to the single block that dominates
// the entire loop.
// We rotate the conditional test from loop header to loop latch, incoming argument
// of conditional test should be updated as well otherwise we would lose one update.
// At this point, loop latch determines whether loop continues or exits based on
// rotated test.
//
//	  entry
//	    │
//	    │
//	    │
//	    ▼
//	loop header◄──┐
//	    │         │
//	    │         │
//	    │         │
//	    ▼         │
//	loop body     │
//	    │         │
//	    │         │
//	    │         │
//	    ▼         │
//	loop latch────┘
//	    │
//	    │
//	    │
//	    ▼
//	loop exit
//
// Now loop header and loop body are executed unconditionally, this may changes
// program semantics while original program executes them only if test is okay.
// An additional loop guard is required to ensure this.
//
//	     entry
//	       │
//	       │
//	       │
//	       ▼
//	┌───loop guard
//	│      │
//	│      │
//	│      │
//	│      │
//	│      ▼
//	│  loop header◄──┐
//	│      │         │
//	│      │         │
//	│      │         │
//	│      ▼         │
//	│  loop body     │
//	│      │         │
//	│      │         │
//	│      │         │
//	│      ▼         │
//	│  loop latch────┘
//	│      │
//	│      │
//	│      │
//	│	   │
//	│      ▼
//	└─► loop exit
//
// Loop header no longer dominates the entire loop, loop guard dominates it instead.
// If Values defined in the loop were used outside loop, all these uses should be
// replaced by a new Phi node at loop exit which merges control flow from loop
// header and loop guard. This implies that the loop header used to dominate the
// entire loop, including all loop exits. However, this may not always hold true
// for some exotic loop exits. It is necessary to check this before rotation.
//
// The detailed algorithm is summarized as following steps
//
//  1. Check whether loop can apply loop rotate
//     * Loop must be a natural loop and have a single exit and so on..
//     * Collect all values defined within a loop and used outside of the loop.
//     I place it earlier because currently it cannot handle a value outside of
//     a loop that depends on a non-Phi value defined within the loop, it should
//     bail out compilation in such cases.
//
//  2. Rotate condition and rewire loop edges
//     * Move conditional test from loop header to loop latch.
//     * Rewire loop header to loop body unconditionally.
//     * Rewire loop latch to header and exit based on new coming conditional test.
//     * Create new loop guard block and wire it to appropriate blocks.
//
//  3. Update data dependencies after CFG transformation
//     * Update cond to use updated Phi as arguments.
//     * Merge any uses outside loop as loop header may not dominate them anymore.
//     This relies on the value collected in the first step.
func (loop *loop) buildLoopForm(fn *Func) string {
	if loop.outer != nil {
		// TODO: 太过严格，考虑放松？
		return "loop contains loop case"
	}

	loopHeader := loop.header
	// loopHeader <- entry(0), loopLatch(1)?
	// loopHeader -> loopBody(0), loopExit(1)?
	if len(loopHeader.Preds) != 2 || len(loopHeader.Succs) != 2 ||
		loopHeader.Kind != BlockIf {
		return "illegal loop header"
	}
	fn.loopnest().findExits() // initialize loop exits
	loopExit := loop.header.Succs[1].b
	loop.exit = loopExit
	loop.latch = loopHeader.Preds[1].b
	loop.body = loopHeader.Succs[0].b

	if len(loopExit.Preds) != 1 {
		// TODO: 太过严格，考虑放松？
		return "loop exit requries 1 predecessor"
	}

	if len(loop.exits) != 1 {
		// FIXME: 太过严格，考虑放松？
		for _, exit := range loop.exits {
			if exit == loopExit {
				continue
			}
			if !fn.Sdom().IsAncestorEq(loopHeader, exit) {
				return "loop exit is not dominated by header"
			}
			if len(exit.Succs) != 0 {
				return "loop exit must end cfg"
			}
		}
	}

	illForm := true
	for _, exit := range loop.exits {
		if exit == loopExit {
			illForm = false
			break
		}
	}
	if illForm {
		// TODO: 太过严格，考虑放松？
		return "loop exit is invalid"
	}

	return ""
}

// moveCond moves conditional test from loop header to loop latch
func (loop *loop) moveCond() *Value {
	cond := loop.header.Controls[0]
	if cond.Op == OpPhi {
		// In rare case, conditional test is Phi, we can't move it to loop latch
		return cond
	}
	for valIdx, v := range cond.Block.Values {
		if cond != v {
			continue
		}
		cond.moveTo(loop.latch, valIdx)
		break
	}
	return cond
}

// Update uses of conditional test once guardCond is derived from it
// TODO: Maybe mergeLoopUse already covers this?
func (loop *loop) updateCond(cond *Value) {
	// In original while/for loop, a critical edge is inserted at the end of each
	// iteration, and Phi values are updated. All subsequent uses of Phi rely on
	// the updated values. However, when converted to a do-while loop, Phi nodes
	// may be used at the end of each iteration before they are updated.
	// Therefore, we need to replace all subsequent uses of Phi with the use of
	// Phi parameter. This way, it is equivalent to using the updated values of
	// Phi values. Here is an simple example:
	//
	// Before
	//	 loop header:
	//	 v6 = Phi v5 v19
	//	 v8 = IsNonNil v6
	//	 If v8 -> loop latch, loop exit
	//
	//	 loop latch:
	//	 ...
	//	 v19 = Load ptr mem
	//	 Plain -> loop header
	//
	// After
	//	 loop header:
	//	 v6 = Phi v5 v19
	//	 Plain -> loop latch
	//
	//	 loop latch:
	//	 ...
	//	 v19 = Load ptr mem
	//	 v8 = IsNonNil v6
	//	 If v8 -> loop header, loop exit
	//
	// After loop rotation, v8 should use v19 instead of un-updated v6 otherwise
	// it will lose one update. The same occurrence also happens in mergeLoopUse.
	for idx, use := range cond.Args {
		if use.Op == OpPhi && use.Block == loop.header {
			// loopHeader <- entry(0), loopLatch(1)
			newUse := use.Args[1]
			cond.SetArg(idx, newUse)
		}
	}
}

// rewireLoopHeader rewires the loop CFG to the following shape:
//
//	loopHeader -> loopBody
func (loop *loop) rewireLoopHeader() {
	loopHeader := loop.header

	loopHeader.Kind = BlockPlain
	loopHeader.Likely = BranchUnknown
	loopHeader.ResetControls()
	var edge Edge
	for _, succ := range loopHeader.Succs {
		if succ.b == loop.body {
			edge = succ
			break
		}
	}
	loopHeader.Succs = loopHeader.Succs[:1]
	loopHeader.Succs[0] = edge
}

// rewireLoopLatch rewires the loop CFG to the following shape:
//
//	loopLatch -> loopHeader(0), loopExit(1)
func (loop *loop) rewireLoopLatch(ctrl *Value) {
	loopExit := loop.exit
	loopLatch := loop.latch

	loopLatch.Kind = BlockIf
	loopLatch.SetControl(ctrl)
	var idx int
	for i := 0; i < len(loopExit.Preds); i++ {
		if loopExit.Preds[i].b == loop.header {
			idx = i
			break
		}
	}
	loopLatch.Succs = append(loopLatch.Succs, Edge{loopExit, idx})
	loopExit.Preds[idx] = Edge{loopLatch, 1}
}

// rewireLoopGuard rewires the loop CFG to the following shape:
//
//	loopGuard -> loopHeader(0), loopExit(1)
func (loop *loop) rewireLoopGuard(sdom SparseTree, guardCond *Value) {
	loopHeader := loop.header
	loopGuard := loop.guard
	entry := sdom.Parent(loopHeader)

	loopGuard.Likely = BranchLikely // loop is prefer to be executed at least once
	loopGuard.SetControl(guardCond)
	var idx int
	for i := 0; i < len(loopHeader.Preds); i++ {
		if loopHeader.Preds[i].b == entry {
			idx = i
			break
		}
	}
	loopGuard.Succs = append(loopGuard.Succs, Edge{loopHeader, idx})
	loopGuard.AddEdgeTo(loop.exit)
	loopHeader.Preds[idx] = Edge{loopGuard, 0}
}

// rewireLoopEntry rewires the loop CFG to the following shape:
//
//	loopEntry -> loopGuard
func (loop *loop) rewireLoopEntry(sdom SparseTree, loopGuard *Block) {
	entry := sdom.Parent(loop.header)
	entry.Succs = entry.Succs[:0]
	entry.AddEdgeTo(loopGuard)
}

// createLoopGuard creates loop guard and wires loop CFG to the following shape:
//
//	loopEntry -> loopGuard
//	loopGuard -> loopHeader(0), loopExit(1)
func (loop *loop) createLoopGuard(fn *Func, cond *Value) {
	// Create loop guard block
	// TODO: 现在新插入的loop guard位于最后一个block，放到loop header之前更好
	// we may use it later(in mergeLoopUse)
	loopGuard := fn.NewBlock(BlockIf)
	loop.guard = loopGuard
	sdom := fn.Sdom()

	// Rewire entry to loop guard instead of original loop header
	loop.rewireLoopEntry(sdom, loopGuard)

	// Create conditional test for loop guard based on existing conditional test
	// TODO: 如果已经存在类似loop guard的结构，就无须插入，比如用户已经这么写了：
	//  if len(b) >0 {
	//		for i:=0; i<len(b); i++ {...}
	//  }
	//  这种情况下，我们就不应该插入loop guard
	// TODO: 更新一下新cond的aux信息，比如变量名字，方便debug
	var guardCond *Value
	if cond.Op != OpPhi {
		// Normal case, clone conditional test
		//	  If (Less v1 Phi(v2 v3)) -> loop body, loop exit
		// => If (Less v1 v2)         -> loop header, loop exit
		guardCond = loopGuard.NewValue0IA(cond.Pos, cond.Op, cond.Type, cond.AuxInt, cond.Aux)
		newArgs := make([]*Value, 0, len(cond.Args))
		for _, arg := range cond.Args {
			newArg := arg
			// Dont use Phi, use its incoming value instead, otherwise we will
			// lose one update
			if arg.Block == loop.header && arg.Op == OpPhi {
				newArg = arg.Args[0]
			}
			if !sdom.IsAncestorEq(newArg.Block, cond.Block) {
				panic("new argument of guard cond must dominate old cond")
			}
			newArgs = append(newArgs, newArg)
		}
		guardCond.AddArgs(newArgs...)
	} else {
		// We cannot directly copy it as loop guard cond as we usually do because
		// it is obviously a Phi, and its uses may not dominate the loop guard.
		// For this case, a key observation is whether the loop only executes once,
		// which depends on the first parameter defined in loop entry of the Phi.
		// Therefore, we can directly use this parameter as loop guard cond.
		//
		// Rare case
		//	   If (Phi v1 v2) -> loop body, loop exit
		// =>  If v1          -> loop header, loop exit
		entryArg := cond.Args[0]
		guardCond = entryArg
		if !sdom.IsAncestorEq(entryArg.Block, loop.header) {
			panic("arg of Phi cond must dominate loop header")
		}
	}

	// Rewire loop guard to original loop header and loop exit
	loop.rewireLoopGuard(fn.Sdom(), guardCond)
}

type loopDep struct {
	val  *Value // use value
	idx  int    // index of use value if it's a Phi, otherwise -1
	ctrl *Block // block control values uses loop def
}

// 33064/36000 rotatable/un-rotatable before lower
func (loop *loop) collectLoopUse(fn *Func) (map[*Value][]loopDep, bool) {
	defUses := make(map[*Value][]loopDep, 0)
	bad := make(map[*Value]bool)
	sdom := fn.Sdom()

	for _, val := range loop.header.Values {
		if val.Op == OpPhi {
			defUses[val] = make([]loopDep, 0, val.Uses)
		} else {
			bad[val] = true
		}
	}

	// TODO: 代码美化
	for _, block := range fn.Blocks {
		for _, val := range block.Values {
			for idx, arg := range val.Args {
				if _, exist := defUses[arg]; exist {
					if sdom.IsAncestorEq(loop.exit, block) {
						defUses[arg] = append(defUses[arg], loopDep{val, -1, nil})
					} else if val.Op == OpPhi && sdom.IsAncestorEq(loop.exit, block.Preds[idx].b) {
						defUses[arg] = append(defUses[arg], loopDep{val, idx, nil})
					} else {
						if !sdom.IsAncestorEq(loop.header, block) {
							return nil, true
						}
					}
				} else if _, exist := bad[arg]; exist {
					// Use value other than Phi? We are incapable of handling
					// this case, so we bail out
					return nil, true
				}
			}
		}
		if sdom.IsAncestorEq(loop.exit, block) {
			for _, ctrl := range block.ControlValues() {
				if _, exist := defUses[ctrl]; exist {
					defUses[ctrl] = append(defUses[ctrl], loopDep{nil, -1, block})
				} else if _, exist := bad[ctrl]; exist {
					// Use value other than Phi? We are incapable of handling
					// this case, so we bail out
					return nil, true
				}
			}
		}
	}
	return defUses, false
}

func allocMergePhi(fn *Func, loopDef *Value, loopGuard *Block) *Value {
	phi := fn.newValueNoBlock(OpPhi, loopDef.Type, loopDef.Pos)
	if len(loopDef.Block.Preds) != 2 {
		panic("loop header must be 2 pred ")
	}
	var phiArgs [2]*Value
	// loopExit <- loopLatch(0), loopGuard(1)
	for k := 0; k < len(loopDef.Block.Preds); k++ {
		// argument block of use must dominate loopGuard
		if fn.Sdom().IsAncestorEq(loopDef.Block.Preds[k].b, loopGuard) {
			phiArgs[1] = loopDef.Args[k]
		} else {
			phiArgs[0] = loopDef.Args[k]
		}
	}
	phi.AddArgs(phiArgs[:]...)
	return phi
}

func (loop *loop) mergeLoopUse(fn *Func, defUses map[*Value][]loopDep) {
	// Sort defUses so that we have consistent results for multiple compilations.
	loopDefs := make([]*Value, 0)
	for k, _ := range defUses {
		loopDefs = append(loopDefs, k)
	}
	sort.SliceStable(loopDefs, func(i, j int) bool {
		return loopDefs[i].ID < loopDefs[j].ID
	})

	for _, loopDef := range loopDefs {
		loopDeps := defUses[loopDef]
		// No use? Good, nothing to do
		if len(loopDeps) == 0 {
			continue
		}

		phi := allocMergePhi(fn, loopDef, loop.guard)
		for _, loopDep := range loopDeps {
			useValue := loopDep.val
			if useValue != nil {
				if loopDep.idx == -1 {
					for idx, arg := range useValue.Args {
						if arg == loopDef {
							useValue.SetArg(idx, phi)
						}
					}
				} else {
					if useValue.Op != OpPhi {
						panic("must be phi")
					}
					useValue.SetArg(loopDep.idx, phi)
				}
				fmt.Printf("Replace loop def %v with new %v in %v\n",
					loopDef, phi, loopDep.val)
			} else {
				// block ctrl values relies on loop def
				useBlock := loopDep.ctrl
				for i, v := range useBlock.ControlValues() {
					if v == loopDef {
						useBlock.ReplaceControl(i, phi)
						fmt.Printf("Replace loop def %v with new %v in block ctrl %v\n",
							loopDef, phi, loopDep.ctrl)
					}
				}
			}
		}
		loop.exit.placeValue(phi) // move phi into block after replacement
	}
}

func (loop *loop) verifyRotatedForm() {
	if len(loop.header.Succs) != 1 || len(loop.exit.Preds) != 2 ||
		len(loop.latch.Succs) != 2 || len(loop.guard.Succs) != 2 {
		panic("Bad shape after rotation")
	}
}

func (loop*loop) IsRotatedForm() {
	if loop.guard == nil {
		return false
	}
		// TODO: IF DEBUG
		loop.verifyRotatedForm()
	return true
}

//	     entry
//	       │
//	       │
//	       │
//	       ▼
//	┌───loop guard
//	│      │
//	│      │
//	│      ▼
//	|  loop land <= safe land to place Values
//	│      │
//	│      │
//	│      ▼
//	│  loop header◄──┐
//	│      │         │
//	│      │         │
//	│      │         │
//	│      ▼         │
//	│  loop body     │
//	│      │         │
//	│      │         │
//	│      │         │
//	│      ▼         │
//	│  loop latch────┘
//	│      │
//	│      │
//	│      │
//	│	   │
//	│      ▼
//	└─► loop exit
//
func (loop *loop) CreateLoopLand(fn* Func) bool {
	if !loop.IsRotatedForm() {
		return false
	}

	loopGuard := loop.guard
	loopHeader := loop.header
	loopLand := fn.NewBlock(BlockIf)
	loop.land = loopLand

	edgeFound := 0
	for idx, succ:= range loopGuard {
		if succ.b == loopHeader {
			succ.b = loopLand
			succ.i = 0
			loopLand.Preds = append(loopLand.Preds, Edge{loopGuard, idx})
			edgeFound++
			break
		}
	}
	for idx, pred:= range loopHeader {
		if pred.b == loopGuard {
			pred.b = loopLand
			pred.i = 0
			loopLand.Succs = appead(loopLand.Succs, Edge{loopHeader, idx})
			edgeFound++
			break
		}
	}

	if edgeFound !=2 {
		panic("edges are not found between header and guard after rotation")
	}
	return true
}

// TODO: 插入必要的assert
// TODO: 新增测试用例
// TODO: 压力测试，在每个pass之后都执行loop rotate；执行多次loop rotate；打开ssacheck；确保无bug
// TODO: 尽可能放松buildLoopForm限制
func (fn *Func) RotateLoop(loop *loop) bool {
	// if fn.Name != "value" {
	// 	return false
	// }

	// Try to build loop form and bail out if failure
	if msg := loop.buildLoopForm(fn); msg != "" {
		fmt.Printf("Bad %v for rotation: %s %v\n", loop.LongString(), msg, fn.Name)
		return false
	}

	// Collect all use blocks that depend on Value defined inside loop
	defUses, bailout := loop.collectLoopUse(fn)
	if bailout {
		fmt.Printf("Bad %v for rotation: use bad %v\n", loop.LongString(), fn.Name)
		return false
	}

	// Move conditional test from loop header to loop latch
	cond := loop.moveCond()

	// Rewire loop header to loop body unconditionally
	loop.rewireLoopHeader()

	// Rewire loop latch to header and exit based on new conditional test
	loop.rewireLoopLatch(cond)

	// Create new loop guard block and wire it to appropriate blocks
	loop.createLoopGuard(fn, cond)

	// Update cond to use updated Phi as arguments
	loop.updateCond(cond)

	// Merge any uses outside loop as loop header doesnt dominate them anymore
	loop.mergeLoopUse(fn, defUses)

	// Gosh, loop is rotated
	loop.verifyRotatedForm()

	fmt.Printf("Loop Rotation %v in %v\n", loop.LongString(), fn.Name)
	return true
}

// blockOrdering converts loops with a check-loop-condition-at-beginning
// to loops with a check-loop-condition-at-end by reordering blocks.
// This helps loops avoid extra unnecessary jumps.
//
//	 loop:
//	   CMPQ ...
//	   JGE exit
//	   ...
//	   JMP loop
//	 exit:
//
//	  JMP entry
//	loop:
//	  ...
//	entry:
//	  CMPQ ...
//	  JLT loop
func blockOrdering(f *Func) {
	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}

	idToIdx := f.Cache.allocIntSlice(f.NumBlocks())
	defer f.Cache.freeIntSlice(idToIdx)
	for i, b := range f.Blocks {
		idToIdx[b.ID] = i
	}

	// Set of blocks we're moving, by ID.
	move := map[ID]struct{}{}

	// Map from block ID to the moving blocks that should
	// come right after it.
	after := map[ID][]*Block{}

	// Check each loop header and decide if we want to move it.
	for _, loop := range loopnest.loops {
		b := loop.header
		var p *Block // b's in-loop predecessor
		for _, e := range b.Preds {
			if e.b.Kind != BlockPlain {
				continue
			}
			if loopnest.b2l[e.b.ID] != loop {
				continue
			}
			p = e.b
		}
		if p == nil || p == b {
			continue
		}
		after[p.ID] = []*Block{b}
		for {
			nextIdx := idToIdx[b.ID] + 1
			if nextIdx >= len(f.Blocks) { // reached end of function (maybe impossible?)
				break
			}
			nextb := f.Blocks[nextIdx]
			if nextb == p { // original loop predecessor is next
				break
			}
			if loopnest.b2l[nextb.ID] == loop {
				after[p.ID] = append(after[p.ID], nextb)
			}
			b = nextb
		}
		// Swap b and p so that we'll handle p before b when moving blocks.
		f.Blocks[idToIdx[loop.header.ID]] = p
		f.Blocks[idToIdx[p.ID]] = loop.header
		idToIdx[loop.header.ID], idToIdx[p.ID] = idToIdx[p.ID], idToIdx[loop.header.ID]

		// Place b after p.
		for _, b := range after[p.ID] {
			move[b.ID] = struct{}{}
		}
	}

	// Move blocks to their destinations in a single pass.
	// We rely here on the fact that loop headers must come
	// before the rest of the loop.  And that relies on the
	// fact that we only identify reducible loops.
	j := 0
	// Some blocks that are not part of a loop may be placed
	// between loop blocks. In order to avoid these blocks from
	// being overwritten, use a temporary slice.
	oldOrder := f.Cache.allocBlockSlice(len(f.Blocks))
	defer f.Cache.freeBlockSlice(oldOrder)
	copy(oldOrder, f.Blocks)
	for _, b := range oldOrder {
		if _, ok := move[b.ID]; ok {
			continue
		}
		f.Blocks[j] = b
		j++
		for _, a := range after[b.ID] {
			f.Blocks[j] = a
			j++
		}
	}
	if j != len(oldOrder) {
		f.Fatalf("bad reordering in looprotate")
	}
}
