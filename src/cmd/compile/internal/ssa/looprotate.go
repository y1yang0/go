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
//	     ▼  ▼      ▲
//	loop header    │
//	     │  │      │
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
// Now loop header and loop body are executed unconditionally, this changes program
// semantics while original program executes them only if test is okay. An additional
// loop guard is required to ensure this.
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
// The algorithms are summarized as follow steps
//  1. Move conditional test from loop header to loop latch, this is so-called the "rotation"
//  2. Rewire loop header to loop body unconditionally
//     3.
func moveValue(block *Block, val *Value) {
	for valIdx, v := range val.Block.Values {
		if val != v {
			continue
		}
		val.moveTo(block, valIdx)
		break
	}
}

func (block *Block) resetBlockIf(ctrl *Value, s1, s2 *Block) {
	for len(block.Succs) > 0 {
		// remove all successors and keep Phi as it is
		block.removeEdgeOnly(0)
	}
	block.Kind = BlockIf
	block.SetControl(ctrl)
	block.Succs = block.Succs[:0]
	block.AddEdgeTo(s1)
	block.AddEdgeTo(s2)
}

func (block *Block) resetBlockPlain(s1 *Block) {
	for len(block.Succs) > 0 {
		block.removeEdgeOnly(0)
	}
	block.Kind = BlockPlain
	block.Likely = BranchUnknown
	block.ResetControls()
	block.Succs = block.Succs[:0]
	block.AddEdgeTo(s1)
}

func checkLoopForm(loop *loop) bool {
	loopHeader := loop.header
	if loopHeader.Kind != BlockIf {
		return false
	}
	if len(loopHeader.Preds) != 2 {
		return false
	}
	loopExit := loop.header.Succs[1].b
	illShape := true
	for _, exit := range loop.exits {
		if exit == loopExit {
			illShape = false
			break
		}
	}
	if illShape {
		return false
	}
	return true
}

func createLoopGuardCond(loopGuard *Block, cond *Value) *Value {
	guardCond := loopGuard.NewValue0IA(cond.Pos, cond.Op, cond.Type, cond.AuxInt, cond.Aux)
	newArgs := make([]*Value, 0, len(cond.Args))
	for _, arg := range cond.Args {
		if arg.Op == OpPhi {
			fmt.Printf("%v\n", arg.Args[0].LongString())
			newArgs = append(newArgs, arg.Args[0])
		} else {
			fmt.Printf("%v\n", arg.LongString())
			newArgs = append(newArgs, arg)
		}
	}
	guardCond.AddArgs(newArgs...)
	return guardCond
}

func loopRotate(loopnest *loopnest, loop *loop) bool {
	if loopnest.f.Name != "whatthefuck" {
		return false
	}

	// Before rotation, ensure given loop is in form of normal shape
	loopnest.assembleChildren() // initialize loop children
	loopnest.findExits()        // initialize loop exits
	if !checkLoopForm(loop) {
		return false
	}

	fn := loopnest.f
	loopHeader := loop.header
	loopBody := loop.header.Succs[0].b
	loopExit := loopHeader.Succs[1].b
	loopLatch := loopHeader.Preds[1].b // where increment happens

	fmt.Printf("==START cond:%v, exit:%v latch%v, body:%v -- %v\n",
		loopHeader.String(), loopExit.String(), loopLatch.String(),
		loopBody.String(), loopnest.f.Name)

	// Move conditional test from loop header to loop latch
	cond := loopHeader.Controls[0]
	moveValue(loopLatch, cond)

	// Rewire loop header to loop body unconditionally
	loopHeader.resetBlockPlain(loopBody)

	// TODO:VERIFY LOOP FORM

	// Rewire loop latch to header and exit based on new coming conditional test
	loopLatch.resetBlockIf(cond, loopHeader, loopExit)

	// Create new loop guard block and rewire entry block to it
	loopGuard := loopnest.f.NewBlock(BlockIf)
	entry := loopnest.sdom.Parent(loopHeader)
	entry.removeEdgeOnly(0)
	entry.AddEdgeTo(loopGuard)

	// Create conditional test to loop guard based on existing conditional test
	guardCond := createLoopGuardCond(loopGuard, cond)

	// Rewire loop guard to original loop header and loop exit
	loopGuard.SetControl(guardCond)
	loopGuard.AddEdgeTo(loopHeader)
	loopGuard.AddEdgeTo(loopExit)
	loopGuard.Likely = BranchLikely // loop is prefer to be executed at least once
	fmt.Printf("==New guard cond:%v, block:%v\n",
		guardCond.LongString(), loopGuard.LongString())

	// Loop is rotated
	fn.dumpFile("oops")
	fmt.Printf("== Done\n")

	fn.invalidateCFG()
	return true
}

// blockOrdering converts loops with a check-loop-condition-at-beginning
// to loops with a check-loop-condition-at-end.
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
