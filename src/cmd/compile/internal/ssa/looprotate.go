// Copyright 2017 The Go Authors. All rights reserved.
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
// We rotate the conditional test from loop header to loop latch. And loop latch
// determines whether loop continues or exits based on incoming this test.
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
// TODO: 详细描述算法步骤
// TODO: 插入必要的assert
// TODO: 插入必要的debug print
// TODO: 新增IR测试用例looprotate_test.go
// TODO: 在每个pass之后都执行loop rotate，让他更robustness

func (loop *loop) FullString() string {
	// Loop: loop header, B: loop body, E: loop exit, L: loop latch, G: loop guard
	return fmt.Sprintf("Loop@%v(B@%v E@%v L@%v G@%v)",
		loop.header, loop.body, loop.exit, loop.latch, loop.guard)
}

func (ln *loopnest) checkLoopForm(loop *loop) string {
	ln.findExits() // initialize loop exits

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
		// TODO: 太过严格，考虑放松？
		return "loop exit requries 1 predecessor"
	}

	if len(loop.exits) != 1 {
		// FIXME: 太过严格，考虑放松？
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
		// TODO: 太过严格，考虑放松？
		return "loop exit is invalid"
	}

	cond := loopHeader.Controls[0]
	entry := ln.sdom.Parent(loopHeader)
	for _, arg := range cond.Args {
		// TODO: 太过严格，考虑放松？
		// skip cases we couldn't create phi node. like use method calls' result as loop condition.
		if ln.sdom.IsAncestorEq(arg.Block, entry) || arg.Op == OpPhi {
			continue
		}
		return fmt.Sprintf("loop use method calls as cond. %s in block: %s", arg.LongString(), arg.Block.String())
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
	//	 Plain → loop latch
	//
	//	 loop latch:
	//	 ...
	//	 v19 = Load ptr mem
	//	 v8 = IsNonNil v6
	//	 If v8 → loop header, loop exit
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
	// TODO: 如果当前循环是inner loop,就不要插入guard，因为可以保证循环至少执行一次
	// TODO: 更新一下新cond的aux信息，比如变量名字，方便debug
	var guardCond *Value
	if cond.Op != OpPhi {
		// Normal case, e.g. If (Less64 v1 v2) -> loop header, loop exit
		guardCond = loopGuard.NewValue0IA(cond.Pos, cond.Op, cond.Type, cond.AuxInt, cond.Aux)
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
		// Rare case, If (Phi v1 v2) -> loop header, loop exit
		entryArg := cond.Args[0]
		guardCond = entryArg
		if !sdom.IsAncestorEq(entryArg.Block, loop.header) {
			panic("arg of Phi cond must dominate loop header")
		}
	}

	// Rewire loop guard to original loop header and loop exit
	loop.rewireLoopGuard(fn.Sdom(), guardCond)
}

func (loop *loop) collectLoopUse(fn *Func) (map[*Value][]*Block, bool) {
	defUses := make(map[*Value][]*Block)
	bad := make(map[*Value]bool)
	sdom := fn.Sdom()

	// Record all values defined inside loop header, which are used outside loop
	for _, val := range loop.header.Values {
		if val.Op == OpPhi {
			defUses[val] = make([]*Block, 0, val.Uses)
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
						defUses[arg] = append(defUses[arg], val.Block)
					} else if val.Op == OpPhi && sdom.IsAncestorEq(loop.exit, block.Preds[idx].b) {
						defUses[arg] = append(defUses[arg], val.Block)
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
					defUses[ctrl] = append(defUses[ctrl], block)
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

// If the basic block following the loop has value dependencies on the values
// defined within the current loop, it is necessary to create a Phi at the loop
// exit and use it to replace the values defined within the loop. This is because
// after inserting the loop guard, the loop may not always dominate the loop exit,
// loop exit merges control flows from loop guard and loop latch.
func (loop *loop) mergeLoopUse(fn *Func, defUses map[*Value][]*Block) {
	sdom := fn.Sdom()
	for def, useBlock := range defUses {
		if len(useBlock) == 0 {
			continue
		}
		phi := loop.exit.Func.newValueNoBlock(OpPhi, def.Type, def.Pos)
		if len(def.Block.Preds) != 2 {
			fmt.Printf("loop header must be 2 pred %v %v\n", def, loop.FullString())
			panic("loop header must be 2 pred ")
		}
		var phiArgs [2]*Value
		// loopExit <- loopLatch(0), loopGuard(1)
		for k := 0; k < len(def.Block.Preds); k++ {
			// argument block of use must dominate loopGuard
			if sdom.IsAncestorEq(def.Block.Preds[k].b, loop.guard) {
				phiArgs[1] = def.Args[k]
			} else {
				phiArgs[0] = def.Args[k]
			}
		}
		phi.AddArgs(phiArgs[:]...)
		// fmt.Printf("== dep %v is replaced by %v in block%v\n", dep.LongString(), phi.LongString(), blocks)
		for _, block := range useBlock {
			block.replaceUses(def, phi)
		}
		loop.exit.placeValue(phi) // move phi into block after replaceUses
	}
}

func (loopnest *loopnest) rotateLoop(loop *loop) bool {
	// if loopnest.f.Name != "blockGeneric" {
	// 	return false
	// }

	// Before rotation, ensure given loop is in form of natural shape
	if msg := loopnest.checkLoopForm(loop); msg != "" {
		//	fmt.Printf("Loop Rotation: Bad loop L%v: %s \n", loop.header, msg)
		return false
	}

	// Initilaize loop structure
	fn := loopnest.f
	loopHeader := loop.header
	loop.exit = loopHeader.Succs[1].b
	loop.latch = loopHeader.Preds[1].b
	loop.body = loop.header.Succs[0].b

	// Collect all use blocks that depend on Value defined inside loop
	defUses, bailout := loop.collectLoopUse(fn)
	if bailout {
		//fmt.Printf("Unable to process loop use other than Phi\n")
		return false
	}

	// Move conditional test from loop header to loop latch
	cond := loop.moveCond()

	// Rewire loop header to loop body unconditionally
	loop.rewireLoopHeader()

	// Rewire loop latch to header and exit based on new coming conditional test
	loop.rewireLoopLatch(cond)

	// Create new loop guard block and wire it to appropriate blocks
	loop.createLoopGuard(fn, cond)

	// Update cond to use updated Phi as arguments
	loop.updateCond(cond)

	// Merge any uses that not dominated by loop guard to loop exit
	loop.mergeLoopUse(fn, defUses)

	// Gosh, loop is rotated
	// TODO: 新增verifyLoopRotated，验证rotated后的loop形式符合预期
	fmt.Printf("Loop Rotation: %v %v\n", loop.FullString(), fn.Name)
	fn.invalidateCFG()
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
