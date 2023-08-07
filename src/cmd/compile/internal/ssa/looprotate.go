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
// The detailed algorithm is summarized as following steps
//  1. Move conditional test from loop header to loop latch, this is so-called the "rotation"
//  2. Rewire loop header to loop body unconditionally
//  3. Rewire loop latch to header and exit based on new coming conditional test
//  4. Create new loop guard block and rewire entry block to it
//  5. Create conditional test to loop guard based on existing conditional test
//  6. Rewire loop guard to original loop header and loop exit
//  7. Loop is rotated
func moveValue(block *Block, val *Value) {
	for valIdx, v := range val.Block.Values {
		if val != v {
			continue
		}
		val.moveTo(block, valIdx)
		break
	}
}

func rewireLoopHeader(loopHeader *Block, loopBody *Block) bool {
	loopHeader.Kind = BlockPlain
	loopHeader.Likely = BranchUnknown
	loopHeader.ResetControls()

	for _, succ := range loopHeader.Succs {
		if succ.b == loopBody {
			// loopHeader -> loopBody, loopExit
			loopHeader.Succs = loopHeader.Succs[:1]
			loopHeader.Succs[0] = succ
			return true
		}
	}
	return false
}

func rewireLoopLatch(loopLatch *Block, ctrl *Value, loopHeader, loopExit *Block) bool {
	loopLatch.Kind = BlockIf
	loopLatch.SetControl(ctrl)
	for i := 0; i < len(loopExit.Preds); i++ {
		if loopExit.Preds[i].b == loopHeader {
			loopLatch.Succs = append(loopLatch.Succs, Edge{loopExit, i})
			// loopLatch -> loopHeader(0), loopExit(1)
			loopExit.Preds[i] = Edge{loopLatch, 1}
			return true
		}
	}
	return false
}

func rewireLoopGuard(loopGuard *Block, ctrl *Value, entry, loopHeader, loopExit *Block) bool {
	loopGuard.Likely = BranchLikely // loop is prefer to be executed at least once
	loopGuard.SetControl(ctrl)
	loopGuard.AddEdgeTo(loopExit)
	for i := 0; i < len(loopHeader.Preds); i++ {
		if loopHeader.Preds[i].b == entry {
			loopGuard.Succs = append(loopGuard.Succs, Edge{loopHeader, i})
			// loopGuard -> loopExit(0), loopHeader(1)
			loopHeader.Preds[i] = Edge{loopGuard, 1}
			return true
		}
	}
	return false
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
	illForm := true
	for _, exit := range loop.exits {
		if exit == loopExit {
			illForm = false
			break
		}
	}
	if illForm {
		return false
	}
	return true
}

func createLoopGuardCond(loopGuard *Block, cond *Value) *Value {
	guardCond := loopGuard.NewValue0IA(cond.Pos, cond.Op, cond.Type, cond.AuxInt, cond.Aux)
	newArgs := make([]*Value, 0, len(cond.Args))
	for _, arg := range cond.Args {
		if arg.Op == OpPhi {
			newArgs = append(newArgs, arg.Args[0])
		} else {
			newArgs = append(newArgs, arg)
			fmt.Errorf("Not implemented\n")
		}
	}
	guardCond.AddArgs(newArgs...)
	return guardCond
}

func mergeLoopExit(loopExit, loopHeader, loopGuard *Block) {
	for _, val := range loopExit.Values {
		for _, arg := range val.Args {
			if arg.Block == loopHeader {
				if arg.Op == OpPhi {
					// Allocate floating new phi
					phi := loopExit.Func.newValueNoBlock(OpPhi, arg.Type, arg.Pos)
					// loop exit <- loop latch(1), loop guard(2)
					phiArgs := make([]*Value, 0, len(loopExit.Preds))
					phiArgs = append(phiArgs, arg)
					for k := 0; k < len(arg.Block.Preds); k++ {
						if arg.Block.Preds[k].b == loopGuard {
							phiArgs = append(phiArgs, arg.Args[k])
							break
						}
					}
					phi.AddArgs(phiArgs...)
					loopExit.replaceUses(arg, phi)
					loopExit.placeValue(phi) // move phi into loopExit after replaceUses
				} else {
					fmt.Errorf("Not implemented\n")
					// TODO: maybe we need to clone chain values from loop header to loop exit :(
					// OR simply bail out compilation
				}
			}
		}
	}
}

func (loopnest *loopnest) rotateLoop(loop *loop) bool {
	if loopnest.f.Name != "whatthefuck" {
		return false
	}

	// Before rotation, ensure given loop is in form of normal shape
	loopnest.assembleChildren() // initialize loop children
	loopnest.findExits()        // initialize loop exits
	fn := loopnest.f

	if !checkLoopForm(loop) {
		fmt.Printf("Loop Rotation: Loop %v not in form of normal shape\n", loop.header)
		return false
	}

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
	if !rewireLoopHeader(loopHeader, loopBody) {
		fmt.Printf("Loop Rotation: Failed to rewire loop header\n")
		return false
	}

	// Rewire loop latch to header and exit based on new coming conditional test
	if !rewireLoopLatch(loopLatch, cond, loopHeader, loopExit) {
		fmt.Printf("Loop Rotation: Failed to rewire loop latch\n")
		return false
	}

	// Create new loop guard block and rewire entry block to it
	loopGuard := loopnest.f.NewBlock(BlockIf)
	entry := loopnest.sdom.Parent(loopHeader)
	entry.Succs = entry.Succs[:0] // corresponding predecessor edge of loop header should be rewired later
	entry.AddEdgeTo(loopGuard)

	// Create conditional test to loop guard based on existing conditional test
	// TODO: If loop guard is already exists, dont insert duplicate one
	// TODO: If this is inner loop, dont insert loop guard
	loopGuardCond := createLoopGuardCond(loopGuard, cond)

	// Rewire loop guard to original loop header and loop exit
	if !rewireLoopGuard(loopGuard, loopGuardCond, entry, loopHeader, loopExit) {
		fmt.Printf("Loop Rotation: Failed to rewire loop guard\n")
		return false
	}

	// Loop exit now merges loop header and loop guard, so Phi is required if loop exit Values depends on Values that
	// defined in loop header
	mergeLoopExit(loopExit, loopHeader, loopGuard)

	// TODO: Verify rotated loop form

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
