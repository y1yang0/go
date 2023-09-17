// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
)

// ----------------------------------------------------------------------------
// Loop Rotation
//
// Loop rotation transforms while/for loop to do-while style loop. The original
// natural loop is in form of below IR
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
// A so-called loop guard is inserted to ensure loop is executed at least once.
//
//	     entry
//	       │
//	       │
//	       │
//	       ▼
//	┌──loop guard
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
//	│	   │
//	│      ▼
//	└─► loop exit
//
// Loop header no longer dominates the entire loop, loop guard dominates it instead.
// If Values defined in the loop were used outside loop, all these uses should be
// replaced by a new Phi node at loop exit which merges control flow from loop
// header and loop guard. Based on the Loop Close SSA Form, these Phis have already
// been created. All we need to do is reset their operands to accurately reflect
// the fact that loop exit is a merge point now.
//
// One of the main purposes of Loop Rotation is to assist other optimizations
// such as LICM. They may require that the rotated loop has a proper while safe
// block to place new Values, an optional loop land block is hereby created to
// give these optimizations a chance to keep them from being homeless.
//
//	     entry
//	       │
//	       │
//	       │
//	       ▼
//	┌──loop guard
//	│      │
//	│      │
//	│      │
//	│      ▼
//	|  loop land  <= safe land to place Values
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
//	│	   │
//	│      ▼
//	└─► loop exit
//
// The detailed algorithm is summarized as following steps
//
//  0. Transform the loop to Loop Close SSA Form
//     * All uses of loop defined Values will be replaced by uses of close Phis
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
//     * Rewire loop latch to header and exit based on new conditional test.
//     * Create new loop guard block and wire it to appropriate blocks.
//
//  3. Update data dependencies after CFG transformation
//     * Update cond to use updated Phi as arguments.
//     * Update uses of Values defined in loop header as loop header no longer
//     dominates the loop exit

// v4 = Phi
// ...
// v2 = Add v4, v5
// v1 = Add v2, v3
// If v1-> loop exit, loop ex
func isTrivialLoopDef(sdom SparseTree, loopHeader *Block, val *Value, depth int) bool {
	if depth >= 5 {
		return false
	}

	if !isSpeculativeValue(val) {
		return false
	}
	if val.Op == OpPhi && sdom.IsAncestorEq(val.Block, loopHeader) {
		return true
	}
	for _, arg := range val.Args {
		if !isTrivialLoopDef(sdom, loopHeader, arg, depth+1) {
			return false
		}
	}
	return true
}

func cloneTrivialLoopDef(fn *Func, block *Block, sdom SparseTree, loop *loop, val *Value) *Value {
	if val.Block != loop.header && val.Block != loop.latch {
		assert(sdom.isAncestor(val.Block, loop.header), "sanity check")
		return val
	}
	if val.Op == OpPhi {
		for idx, pred := range val.Block.Preds {
			if sdom.isAncestor(pred.b, loop.header) {
				return val.Args[idx]
			}
		}
		panic("NONONO")
	}
	clone := fn.newValueNoBlock(val.Op, val.Type, val.Pos)
	clone.AuxInt = val.AuxInt
	clone.Aux = val.Aux
	args := make([]*Value, len(val.Args))
	for i := 0; i < len(val.Args); i++ {
		args[i] = cloneTrivialLoopDef(fn, block, sdom, loop, val.Args[i])
	}
	clone.AddArgs(args...)
	block.placeValue(clone)
	return clone
}

func (loop *loop) buildLoopForm(fn *Func) string {
	loopHeader := loop.header
	// loopHeader <- entry(0), loopLatch(1)?
	// loopHeader -> loopBody(0), loopExit(1)?
	if len(loopHeader.Preds) != 2 || len(loopHeader.Succs) != 2 ||
		loopHeader.Kind != BlockIf {
		return "illegal loop header"
	}
	fn.loopnest().findExits() // initialize loop exits
	loopExit := loopHeader.Succs[1].b
	loop.body = loopHeader.Succs[0].b

	found := false
	for _, exit := range loop.exits {
		if exit == loopExit {
			found = true
			break
		}
	}
	if !found {
		loopExit = loopHeader.Succs[0].b
		loop.body = loopHeader.Succs[1].b
	}

	loop.exit = loopExit
	loop.latch = loopHeader.Preds[1].b
	sdom := fn.Sdom()

	if len(loop.exits) != 1 {
		for _, exit := range loop.exits {
			if exit == loopExit {
				continue
			}
			// Loop header may not dominate all loop exist, given up for these
			// exotic guys
			if !sdom.IsAncestorEq(loopHeader, exit) {
				return "loop exit is not dominated by header"
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
		return "loop exit is invalid"
	}

	for ipred, pred := range loop.exit.Preds {
		if pred.b == loop.header {
			for _, val := range loop.exit.Values {
				if val.Op == OpPhi {
					if arg := val.Args[ipred]; arg.Op != OpPhi && arg.Block == loop.header {
						// fmt.Printf("==XX1 %v\n", isTrivialLoopDef(sdom, loopHeader, val.Args[0], 0))
						return "use other phi"
					}
				}
			}
			break
		}
	}

	for _, ctrl := range loop.header.ControlValues() {
		if ctrl.Uses > 1 {
			return "cond has many users"
		}
		for _, arg := range ctrl.Args {
			if arg.Block == loop.header && arg.Op != OpPhi {
				// fmt.Printf("==XX2 %v\n", isTrivialLoopDef(sdom, loopHeader, arg, 0))
				return "cond relies not phi"
			}
		}
	}
	return ""
}

// moveCond moves conditional test from loop header to loop latch
func (loop *loop) moveCond() *Value {
	// TODO: 移动后必须要保证loop cond的arg支配当前loop cond
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
	// it will lose one update. The same occurrence also happens in updateLoopUse.
	for idx, use := range cond.Args {
		if use.Op == OpPhi && use.Block == loop.header {
			// loopHeader <- entry(0), loopLatch(1)
			newUse := use.Args[1]
			cond.SetArg(idx, newUse)
		}
	}
}

func (loop *loop) rewireLoopHeader(exitIdx int) {
	loopHeader := loop.header
	loopHeader.Reset(BlockPlain)

	e := loopHeader.Succs[1-exitIdx]
	// loopHeader -> loopBody(0)
	loopHeader.Succs = loopHeader.Succs[:1]
	loopHeader.Succs[0] = e
}

func (loop *loop) rewireLoopLatch(ctrl *Value, exitIdx int) {
	loopExit := loop.exit
	loopLatch := loop.latch
	loopHeader := loop.header
	loopLatch.resetWithControl(BlockIf, ctrl)
	loopLatch.Likely = loopHeader.Likely
	loopHeader.Likely = BranchUnknown

	var idx int
	for i := 0; i < len(loopExit.Preds); i++ {
		if loopExit.Preds[i].b == loop.header {
			idx = i
			break
		}
	}
	if exitIdx == 1 {
		//loopLatch -> loopHeader(0), loopExit(1)
		loopLatch.Succs = append(loopLatch.Succs, Edge{loopExit, idx})
	} else {
		//loopLatch -> loopExit(0), loopHeader(1)
		loopLatch.Succs = append([]Edge{{loopExit, idx}}, loopLatch.Succs[:]...)
	}
	// loopExit <- loopLatch, ...
	loopExit.Preds[idx] = Edge{loopLatch, exitIdx}
	// loopHeader <- loopLatch, ...
	for i := 0; i < len(loopHeader.Preds); i++ {
		if loopHeader.Preds[i].b == loopLatch {
			idx = i
			break
		}
	}
	loopHeader.Preds[idx] = Edge{loopLatch, 1 - exitIdx}
}

func (loop *loop) rewireLoopGuard(sdom SparseTree, guardCond *Value, exitIdx int) {
	loopHeader := loop.header
	loopGuard := loop.guard
	loopExit := loop.exit
	loopGuard.Pos = loopHeader.Pos
	loopGuard.Likely = loopHeader.Likely // respect header's branch predication
	loopGuard.SetControl(guardCond)

	var idx int
	for i := 0; i < len(loopHeader.Preds); i++ {
		if loopHeader.Preds[i].b == sdom.Parent(loopHeader) {
			idx = i
			break
		}
	}

	numExitPred := len(loopExit.Preds)
	if exitIdx == 1 {
		// loopGuard -> loopHeader(0), loopExit(1)
		loopGuard.Succs = append(loopGuard.Succs, Edge{loopHeader, idx})
		loopGuard.Succs = append(loopGuard.Succs, Edge{loopExit, numExitPred})
		loopExit.Preds = append(loopExit.Preds, Edge{loopGuard, 1})
		loopHeader.Preds[idx] = Edge{loopGuard, 0}
	} else {
		// loopGuard -> loopExit(0), loopHeader(1)
		loopGuard.Succs = append(loopGuard.Succs, Edge{loopExit, numExitPred})
		loopGuard.Succs = append(loopGuard.Succs, Edge{loopHeader, idx})
		loopExit.Preds = append(loopExit.Preds, Edge{loopGuard, 0})
		loopHeader.Preds[idx] = Edge{loopGuard, 1}
	}
}

func (loop *loop) rewireLoopEntry(sdom SparseTree, loopGuard *Block) {
	entry := sdom.Parent(loop.header)
	// loopEntry -> loopGuard
	entry.Succs = entry.Succs[:0]
	entry.AddEdgeTo(loopGuard)
}

// Clone old conditional test and its arguments to control loop guard
func (loop *loop) cloneCond(fn *Func, sdom SparseTree, cond *Value) *Value {
	var guardCond *Value
	if cond.Op != OpPhi {
		// Normal case, clone conditional test
		//	  If (Less v1 Phi(v2 v3)) -> loop body, loop exit
		// => If (Less v1 v2)         -> loop header, loop exit
		// guardCond = loopGuard.NewValue0IA(cond.Pos, cond.Op, cond.Type, cond.AuxInt, cond.Aux)
		// newArgs := make([]*Value, 0, len(cond.Args))
		// for _, arg := range cond.Args {
		// 	newArg := arg
		// 	// Dont use Phi, use its incoming value instead, otherwise we will
		// 	// lose one update
		// 	if arg.Block == loop.header && arg.Op == OpPhi {
		// 		newArg = arg.Args[0]
		// 	}
		// 	if !sdom.IsAncestorEq(newArg.Block, cond.Block) {
		// 		panic("new argument of guard cond must dominate old cond")
		// 	}
		// 	newArgs = append(newArgs, newArg)
		// }
		// guardCond.AddArgs(newArgs...)
		guardCond = cloneTrivialLoopDef(fn, loop.guard, sdom, loop, cond)
	} else {
		// Rare case
		//	   If (Phi v1 v2) -> loop body, loop exit
		// =>  If v1          -> loop header, loop exit
		entryArg := cond.Args[0]
		guardCond = entryArg
		if !sdom.IsAncestorEq(entryArg.Block, loop.header) {
			panic("arg of Phi cond must dominate loop header")
		}
	}
	return guardCond
}

func (loop *loop) updateLoopUse(fn *Func) {
	fn.invalidateCFG()
	sdom := fn.Sdom()
	loopExit := loop.exit
	for _, val := range loopExit.Values {
		if val.Op == OpPhi {
			assert(len(val.Args) == len(loopExit.Preds)-1, "less than loop exit preds")
			// fmt.Printf("==BEF %v\n", val.LongString())
			newArgs := make([]*Value, len(loopExit.Preds))
			var newPathArg *Value // new guard to exit path
			for iarg, arg := range val.Args {
				newArgs[iarg] = arg
				exitPred := loopExit.Preds[iarg].b
				if loop.latch == exitPred {
					// header->exit => latch->exit, update loop use
					if sdom.isAncestor(arg.Block, loop.header) {
						newPathArg = arg
					} else if arg.Block == loop.header {
						assert(arg.Op == OpPhi, "use other than phi")
						guardIdx := 0
						if loop.header.Preds[0].b == loop.latch {
							guardIdx = 1 // then index 1 is loop guard
						}
						backedgeArg := arg.Args[1-guardIdx]
						newArgs[iarg] = backedgeArg
						newPathArg = arg.Args[guardIdx]
					} else {
						panic("can not image")
					}
				}
			}

			if newPathArg != nil {
				newArgs[len(loop.exit.Preds)-1] = newPathArg
				val.resetArgs()
				val.AddArgs(newArgs...)
				// fmt.Printf("==replace phi %v %v\n", val.LongString(), loop.LongString())
			} else {
				fn.Fatalf("Can not determine new arg of Phi for guard to exit path")
			}
		}
	}
}

func (loop *loop) verifyRotatedForm() {
	if len(loop.header.Succs) != 1 || len(loop.exit.Preds) < 2 ||
		len(loop.latch.Succs) != 2 || len(loop.guard.Succs) != 2 {
		panic("Bad shape after rotation")
	}
}

// IsRotatedForm returns true if loop is rotated
func (loop *loop) IsRotatedForm() bool {
	if loop.guard == nil {
		return false
	}
	return true
}

// CreateLoopLand creates a land block between loop guard and loop header, it
// executes only if entering loop.
func (loop *loop) CreateLoopLand(fn *Func) bool {
	if !loop.IsRotatedForm() {
		return false
	}
	if loop.land != nil {
		return true
	}

	// loopGuard -> loopLand
	// loopLand -> loopHeader
	loopGuard := loop.guard
	loopHeader := loop.header
	loopLand := fn.NewBlock(BlockPlain)
	loopLand.Pos = loopHeader.Pos
	loopLand.Preds = make([]Edge, 1, 1)
	loopLand.Succs = make([]Edge, 1, 1)
	loop.land = loopLand

	loopGuard.ReplaceSucc(loopHeader, loopLand, 0)
	loopHeader.ReplacePred(loopGuard, loopLand, 0)
	return true
}

// TODO: 新增测试用例
// TODO: 压力测试，在每个pass之后都执行loop rotate；执行多次loop rotate；打开ssacheck；确保无bug
// 33064/36000 rotated/bad before lower
// 39022/25245 rotated/bad before lower, lcssa
// 46986/17281 rotated/bad before lower, lcssa
// 47053/17162 rotated/bad before lower, lcssa with arbitary exit order
// 52236/12282 rotated/bad before lower, allow multiple preds of exit
func (fn *Func) RotateLoop(loop *loop) bool {
	if loop.IsRotatedForm() {
		return true
	}
	// if fn.Name != "Name" {
	// 	return false
	// }
	// if fn.Name != "(*regAllocState).liveAfterCurrentInstruction" {
	// 	return false
	// }
	// if fn.Name != "heapBitsSetType" {
	// 	return false
	// }
	// Try to build loop form and bail out if failure
	if msg := loop.buildLoopForm(fn); msg != "" {
		// if fn.pass.debug > 1 {
		fmt.Printf("Bad %v for rotation: %s %v\n", loop.LongString(), msg, fn.Name)
		// }
		return false
	}

	exitIdx := 1 // which successor of loop header wires to loop exit
	if loop.header.Succs[0].b == loop.exit {
		exitIdx = 0
	}

	// Move conditional test from loop header to loop latch
	cond := loop.moveCond()

	// Rewire loop header to loop body unconditionally
	loop.rewireLoopHeader(exitIdx)

	// Rewire loop latch to header and exit based on new conditional test
	loop.rewireLoopLatch(cond, exitIdx)

	// Create loop guard block
	// TODO(yyang): Creation of loop guard can be skipped if original IR already
	// exists such form. e.g. if 0 < len(b) { for i := 0; i < len(b); i++ {...} }
	loopGuard := fn.NewBlock(BlockIf)
	loop.guard = loopGuard
	sdom := fn.Sdom()

	// Rewire entry to loop guard instead of original loop header
	loop.rewireLoopEntry(sdom, loopGuard)

	// Clone old conditional test and its arguments to control loop guard
	guardCond := loop.cloneCond(fn, sdom, cond)

	// Rewire loop guard to original loop header and loop exit
	loop.rewireLoopGuard(fn.Sdom(), guardCond, exitIdx)

	// Update cond to use updated Phi as arguments
	loop.updateCond(cond)

	// Update loop uses as loop header no longer dominates exit
	loop.updateLoopUse(fn)

	// Gosh, loop is rotated
	loop.verifyRotatedForm()

	// if fn.pass.debug > 1 {
	fmt.Printf("%v rotated in %v\n", loop.LongString(), fn.Name)
	// }
	fn.invalidateCFG()
	return true
}

// layoutLoop converts loops with a check-loop-condition-at-beginning
// to loops with a check-loop-condition-at-end by reordering blocks. no
// CFG changes here. This helps loops avoid extra unnecessary jumps.
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
func layoutLoop(f *Func) {
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
		// if b.Kind == BlockPlain {
		// 	// Real loop rotation already applied?
		// 	continue
		// }
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
