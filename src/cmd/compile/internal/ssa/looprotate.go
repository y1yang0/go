// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "fmt"

// ----------------------------------------------------------------------------
// Loop Rotation
//
// Loop rotation transforms while/for loop to do-while style loop. The original
// normal loop is in form of below shape
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
// Then we rotate its conditional test from loop header to loop latch. And loop
// latch determines whether loop continues or exits based on incoming test
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
//	    entry
//	      │
//	      │
//	      │
//	      ▼
//	  loop guard
//	   │  │
//	   │  │
//	   │  │  ┌────┐
//	┌──┘  │  │    │
//	│     ▼  ▼    │
//	│ loop header │
//	│     │       │
//	│     │       │
//	│     │       │
//	│     ▼       │
//	│ loop body   │
//	│     │       │
//	│     │       │
//	│     │       │
//	│     ▼       │
//	│ loop latch  │
//	│     │  │    │
//	│     │  │    │
//	└──┐  │  └────┘
//	   │  │
//	   ▼  ▼
//	  loop exit
//
// The detailed algorithm is summarized as following steps
//  1. Move conditional test from loop header to loop latch, this is so-called the "rotation"
//  2. Rewire loop header to loop body unconditionally
//  3. Rewire loop latch to header and exit based on new coming conditional test
//  4. Create new loop guard block and rewire entry block to it
//  5. Create conditional test to loop guard based on existing conditional test
//  6. Rewire loop guard to original loop header and loop exit
//  7. Loop is rotated

type loopForm struct {
	ln         *loopnest
	loop       *loop
	loopHeader *Block
	loopBody   *Block
	loopExit   *Block
	loopLatch  *Block // where increment happens
	loopGuard  *Block
}

func (lf *loopForm) LongString() string {
	return fmt.Sprintf("Loop %v(B@%v E@%v L@%v G@%v)",
		lf.loopHeader, lf.loopBody, lf.loopExit, lf.loopLatch, lf.loopGuard)
}

func (ln *loopnest) checkLoopForm(loop *loop) string {
	loopHeader := loop.header
	// loopHeader <- entry(0), loopLatch(1)?
	if len(loopHeader.Preds) != 2 {
		return "loop header requires 2 predecessors"
	}
	// loopHeader -> loopBody(0), loopExit(1) ?
	if loopHeader.Kind != BlockIf {
		return "loop header must be BlockIf"
	}
	loopExit := loop.header.Succs[1].b
	if len(loopExit.Preds) != 1 {
		// TODO: Maybe this is too strict
		return "loop exit requries 1 predecessor"
	}

	if len(loop.exits) != 1 {
		// TODO: Maybe this is too strict
		return "loop exit more than one."
	}

	illForm := true
	for _, exit := range loop.exits {
		if exit == loopExit {
			illForm = false
			break
		}
	}
	if illForm {
		// TODO: Maybe this is too strict
		return "loop exit is invalid"
	}

	cond := loopHeader.Controls[0]
	entry := ln.sdom.Parent(loopHeader)
	for _, arg := range cond.Args {
		// skip cases we couldn't create phi node. like use method calls' result as loop condition.
		if ln.sdom.IsAncestorEq(arg.Block, entry) || arg.Op == OpPhi {
			continue
		}
		return fmt.Sprintf("loop use method calls as cond. %s in block: %s", arg.LongString(), arg.Block.String())
	}
	return ""
}

func (lf *loopForm) moveCond() *Value {
	// Move conditional test from loop header to loop latch
	cond := lf.loopHeader.Controls[0]
	for valIdx, v := range cond.Block.Values {
		if cond != v {
			continue
		}
		cond.moveTo(lf.loopLatch, valIdx)
		break
	}
	return cond
}

func (lf *loopForm) updateCond(cond *Value) {
	// Update uses of conditional test once moved
	//
	// loop header:
	// v6 (76) = Phi <*st> v5 v19 (i[*st])
	// Plain → loop latch
	//
	// loop latch:
	// ...
	// v19 (+76) = Load <*st> ptr mem
	// v8 (+76) = IsNonNil <bool> v6
	// If v8 → loop header, loop exit
	for idx, use := range cond.Args {
		if use.Op == OpPhi && use.Block == lf.loopHeader {
			// loopHeader <- entry(0), loopLatch(1)
			newUse := use.Args[1]
			cond.SetArg(idx, newUse)
		}
	}
}

func (lf *loopForm) rewireLoopHeader() {
	loopHeader := lf.loopHeader
	loopBody := lf.loopBody

	loopHeader.Kind = BlockPlain
	loopHeader.Likely = BranchUnknown
	loopHeader.ResetControls()
	var edge Edge
	for _, succ := range loopHeader.Succs {
		if succ.b == loopBody {
			edge = succ
			break
		}
	}
	loopHeader.Succs = loopHeader.Succs[:1]
	// loopHeader -> loopExit(0)
	loopHeader.Succs[0] = edge
}

func (lf *loopForm) rewireLoopLatch(ctrl *Value) {
	loopHeader := lf.loopHeader
	loopExit := lf.loopExit
	loopLatch := lf.loopLatch

	loopLatch.Kind = BlockIf
	loopLatch.SetControl(ctrl)
	var idx int
	for i := 0; i < len(loopExit.Preds); i++ {
		if loopExit.Preds[i].b == loopHeader {
			idx = i
			break
		}
	}
	loopLatch.Succs = append(loopLatch.Succs, Edge{loopExit, idx})
	// loopLatch -> loopHeader(0), loopExit(1)
	loopExit.Preds[idx] = Edge{loopLatch, 1}
}

func (lf *loopForm) rewireLoopGuard(guardCond *Value) {
	loopHeader := lf.loopHeader
	loopExit := lf.loopExit
	loopGuard := lf.loopGuard
	entry := lf.ln.sdom.Parent(loopHeader)

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
	loopGuard.AddEdgeTo(loopExit)
	// loopGuard -> loopHeader(0), loopExit(1)
	loopHeader.Preds[idx] = Edge{loopGuard, 0}
}

func (lf *loopForm) createLoopGuard(cond *Value) *Value {
	// Create loop guard block
	// TODO: insert loop guard before loop header in block order
	loopGuard := lf.ln.f.NewBlock(BlockIf)
	lf.loopGuard = loopGuard
	lf.ln.guards = append(lf.ln.guards, loopGuard)
	sdom := lf.ln.f.Sdom()

	// Rewire entry to loop guard instead of original loop header
	// entry -> loopGuard
	entry := sdom.Parent(lf.loopHeader)
	entry.Succs = entry.Succs[:0]
	entry.AddEdgeTo(loopGuard)

	// Create conditional test for loop guard based on existing conditional test
	// TODO: If loop guard is already exists, dont insert duplicate one
	// TODO: If this is inner loop, dont insert loop guard
	guardCond := loopGuard.NewValue0IA(cond.Pos, cond.Op, cond.Type, cond.AuxInt, cond.Aux)
	newArgs := make([]*Value, 0, len(cond.Args))
	for _, arg := range cond.Args {
		newArg := arg
		// All uses of conditional test should be dominated by test itself, which
		// implies that they should either be located at loopHeader or in a block
		// that is dominated by loopHeader. For the latter case, no further action
		// is needed as it can directly be used as the argument for guardCond
		// For the former case, we need to handle it specially based on the type
		// of the value. For example, we lookup incoming value of Phi as argument
		// of guardCond
		if arg.Block == lf.loopHeader && arg.Op == OpPhi {
			// loopHeader <- entry(0), loopLatch(1)
			newArg = arg.Args[0]
		}
		if !sdom.IsAncestorEq(newArg.Block, cond.Block) {
			panic("new argument of guard cond must dominate old cond")
		}
		newArgs = append(newArgs, newArg)
	}
	guardCond.AddArgs(newArgs...)
	return guardCond
}

// Loop exit now merges loop header and loop guard, so Phi is required if loop
// exit Values depends on Values that defined in loop header
func (lf *loopForm) mergeLoopExit() {
	loopExit := lf.loopExit
	loopGuard := lf.loopGuard
	loopHeader := lf.loopHeader
	sdom := lf.ln.f.Sdom()

	loopBlocks := lf.ln.findLoopBlocks(lf.loop)
	deps := make(map[*Value][]*Block)
	for _, block := range lf.ln.f.Blocks {
		// Is not dominated by loopGuard?
		if sdom.IsAncestorEq(block, loopGuard) {
			continue
		}
		// Is this block belongs to loop?
		foundInLoop := false
		// TODO: this is extremely inefficient
		for _, b := range loopBlocks {
			if b == block {
				foundInLoop = true
				break
			}
		}
		if foundInLoop {
			continue
		}

		// Some value in Block b depends on Value v in current loop
		addDep := func(v *Value, b *Block) {
			// must be loop header
			if v.Block != loopHeader {
				fmt.Printf("use block must be loopHeader%v %v %v\n", loopHeader, v, b)
				panic("ff")
			}
			if v.Op != OpPhi {
				// TODO: maybe we need to clone chain values from loop header to loop exit :(
				// OR simply bail out compilation
				panic("Not implemented yet")
			}
			// Many blocks may rely on identical dep
			deps[v] = append(deps[v], b)
		}

		for _, val := range block.Values {
			for _, arg := range val.Args {
				if lf.ln.b2l[arg.Block.ID] == lf.loop {
					addDep(arg, val.Block)
				}
			}
		}
		for _, ctrl := range block.ControlValues() {
			if lf.ln.b2l[ctrl.Block.ID] == lf.loop {
				addDep(ctrl, block)
			}
		}
	}

	// Create Phi to merge incoming Value and replace dep with new guy.
	// In original while/for loop, a critical edge is inserted at the end of each
	// iteration, and Phi values are updated. All subsequent uses of Phi rely on
	// the updated values. However, when converted to a do-while loop, Phi nodes
	// may be used at the end of each iteration before they are updated.
	// Therefore, we need to replace all subsequent uses of Phi with the use of
	// Phi parameter. This way, it is equivalent to using the updated values of
	// Phi values. Here is an simple example:
	// 	loop header:
	// 		v1 = phi(v2, v3)
	//      Plain -> loop latch
	//
	// 	loop latch:
	// 		v3 = Load v4
	// 		v5 = IsNonNull v1
	// 		If v5 -> loop exit, loop header
	//
	// After loop rotatation, the use of un-updated v1 in v5 remains. We need to
	// replace it with the use of v3.
	for dep, blocks := range deps {
		phi := loopExit.Func.newValueNoBlock(OpPhi, dep.Type, dep.Pos)
		if len(dep.Block.Preds) != 2 {
			panic("loop header must be 2 pred ")
		}
		var phiArgs [2]*Value
		// loopExit <- loopLatch(0), loopGuard(1)
		for k := 0; k < len(dep.Block.Preds); k++ {
			// argument block of use must dominate loopGuard
			if sdom.IsAncestorEq(dep.Block.Preds[k].b, loopGuard) {
				phiArgs[1] = dep.Args[k]
			} else {
				phiArgs[0] = dep.Args[k]
			}
		}
		phi.AddArgs(phiArgs[:]...)
		fmt.Printf("== dep %v is replaced by %v in block%v\n", dep.LongString(), phi.LongString(), blocks)
		for _, block := range blocks {
			block.replaceUses(dep, phi)
		}
		loopExit.placeValue(phi) // move phi into block after replaceUses
	}
}

func (loopnest *loopnest) rotateLoop(loop *loop) bool {
	loopnest.assembleChildren() // initialize loop children
	loopnest.findExits()        // initialize loop exits

	// Before rotation, ensure given loop is in form of normal shape
	if msg := loopnest.checkLoopForm(loop); msg != "" {
		fmt.Printf("Loop Rotation: Bad loop L%v: %s \n", loop.header, msg)
		return false
	}
	if loopnest.f.Name != "InitTables.func3" {
		return false
	}

	loopHeader := loop.header
	lf := &loopForm{
		ln:         loopnest,
		loop:       loop,
		loopHeader: loopHeader,
		loopBody:   loop.header.Succs[0].b,
		loopExit:   loopHeader.Succs[1].b,
		loopLatch:  loopHeader.Preds[1].b,
	}

	// Move conditional test from loop header to loop latch
	cond := lf.moveCond()

	// Rewire loop header to loop body unconditionally
	lf.rewireLoopHeader()

	// Rewire loop latch to header and exit based on new coming conditional test
	lf.rewireLoopLatch(cond)

	// Create new loop guard block and rewire entry block to it
	guardCond := lf.createLoopGuard(cond)

	// Rewire loop guard to original loop header and loop exit
	lf.rewireLoopGuard(guardCond)

	lf.updateCond(cond)
	// Merge any uses in loop exit that not dominated by loop guard
	lf.mergeLoopExit()

	// TODO: Verify rotated loop form

	// Loop is rotated
	f := loopnest.f
	fmt.Printf("Loop Rotation: %v %v\n", lf.LongString(), f.Name)
	f.invalidateCFG()
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
