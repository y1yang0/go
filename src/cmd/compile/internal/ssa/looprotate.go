// Copyright 2023 The Go Authors. All rights reserved.
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
//	│      │
//	│      ▼
//	└─► loop exit
//
// Loop header no longer dominates the entire loop, loop guard dominates it instead.
// If Values defined in the loop were used outside loop, all these uses should be
// replaced by a new Phi node at loop exit which merges control flow from loop
// header and loop guard. Based on the Loop Closed SSA Form, these Phis have already
// been created. All we need to do is simply reset their operands to accurately
// reflect the fact that loop exit is a merge point now.
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
//	│      │
//	│      ▼
//	└─► loop exit
//
// The detailed algorithm is summarized as following steps
//
//  0. Transform the loop to Loop Closed SSA Form
//     * All uses of loop defined Values will be replaced by uses of proxy phis
//
//  1. Check whether loop can apply loop rotate
//     * Loop must be a natural loop and have a single exit and so on..
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

// checkLoopForm checks if loop is well formed and returns failure reason if not
func (loop *loop) checkLoopForm(fn *Func) string {
	loopHeader := loop.header
	// Check if loop header is well formed block
	if len(loopHeader.Preds) != 2 || len(loopHeader.Succs) != 2 ||
		loopHeader.Kind != BlockIf {
		return "illegal loop header"
	}
	fn.loopnest().findExits() // initialize loop exits
	e1, e2 := loopHeader.Succs[1].b, loopHeader.Succs[0].b

	// Check if loop exit nears the loop header
	found := false
	for _, exit := range loop.exits {
		if exit == e1 {
			loop.exit = e1
			loop.body = loopHeader.Succs[0].b
			found = true
			break
		} else if exit == e2 {
			loop.exit = e2
			loop.body = loopHeader.Succs[1].b
			found = true
			break
		}
	}
	if !found {
		return "far loop exit beyond header"
	}

	loop.latch = loopHeader.Preds[1].b
	sdom := fn.Sdom()

	// Check if loop header dominates all loop exits
	if len(loop.exits) != 1 {
		for _, exit := range loop.exits {
			if exit == loop.exit {
				continue
			}
			// Loop header may not dominate all loop exist, given up for these
			// exotic guys
			if !sdom.IsAncestorEq(loopHeader, exit) {
				return "loop exit is not dominated by header"
			}
		}
	}

	// Check if all loop uses are "trivial"
	for _, ctrl := range loop.header.ControlValues() {
		if !isTrivial(sdom, ctrl, loop.header, true, InitDepth) {
			return "non trivial loop cond"
		}
	}
	for ipred, pred := range loop.exit.Preds {
		if pred.b == loop.header {
			for _, val := range loop.exit.Values {
				if val.Op == OpPhi {
					if arg := val.Args[ipred]; arg.Block == loop.header {
						if !isTrivial(sdom, arg, loop.header, false, InitDepth) {
							return "use non trivial loop def outside loop"
						}
					}
				}
			}
			break
		}
	}
	return ""
}

// A loop def is "trivial" if, starting from the value, it is looked up along its
// argument until it encounters the loop phi defined in the loop header, no
// intractable values are encountered in the process, or the lookup depth does
// not exceed the MaxDepth. We need this restriction because all the values in
// the chain from the loop phi to the trivial loop def could be cloned into other
// block, and cloning without careful scrutiny would lead to code bloat and extra
// performance penalty.
const (
	InitDepth = 0
	MaxDepth  = 5
)

type loopTrivialVal struct {
	valBlock *Block
	visited  map[*Value]*Value
}

func isTrivial(sdom SparseTree, val *Value, srcBlock *Block, allowSideEffect bool, depth int) bool {
	if depth >= MaxDepth {
		return false
	}
	if sdom.isAncestor(val.Block, srcBlock) {
		return true
	}
	if val.Op == OpPhi {
		if val.Block == srcBlock {
			return true
		}
		return false
	}
	// if allowSideEffect && val.Uses > 1 {
	// 	return false
	// }
	if !allowSideEffect {
		if val.Op != OpLoad && isAccessMemory(val) {
			return false
		}
	}
	for _, arg := range val.Args {
		if !isTrivial(sdom, arg, srcBlock, allowSideEffect, depth+1) {
			return false
		}
	}
	return true
}

func (t *loopTrivialVal) clone(val *Value, dest *Block, depth int) *Value {
	assert(depth < MaxDepth, "excess max search depth")
	// If seeing Phi or value that lives different from source block? They must
	// not part of trivial loop def chain, do nothing
	if val.Op == OpPhi || val.Block != t.valBlock {
		return val
	}
	// If val is already cloned? Do nothing
	if c, exist := t.visited[val]; exist {
		return c
	}

	// Clone val and its arguments recursively
	clone := dest.Func.newValueNoBlock(val.Op, val.Type, val.Pos)
	clone.AuxInt = val.AuxInt
	clone.Aux = val.Aux
	args := make([]*Value, len(val.Args))
	for i := 0; i < len(val.Args); i++ {
		args[i] = t.clone(val.Args[i], dest, depth+1)
	}
	clone.AddArgs(args...)
	dest.placeValue(clone)
	t.visited[val] = clone // cache cloned value after cloning its arguments
	return clone
}

func (t *loopTrivialVal) move(val *Value, dest *Block, depth int) {
	assert(depth < MaxDepth, "excess max search depth")
	if val.Op == OpPhi || val.Block != t.valBlock {
		return
	}
	for _, arg := range val.Args {
		t.move(arg, dest, depth+1)
	}
	moveTo(val, dest)
	// t.visited[val] = nil // mark as visited
}

func (t *loopTrivialVal) update(val *Value, loopHeader *Block, loopPhiIdx, depth int) {
	assert(depth < MaxDepth, "excess max search depth")
	if val.Op == OpPhi || val.Block != t.valBlock {
		return
	}
	for iarg, arg := range val.Args {
		if arg.Op == OpPhi && arg.Block == loopHeader {
			newUse := arg.Args[loopPhiIdx]
			// loop header:
			//   v1 = Phi v2 v3
			//   ...
			//   v3 = Rsh64x64 v1 ..
			if isomorphic, exist := t.visited[newUse]; !exist {
				val.SetArg(iarg, newUse)
			} else {
				// If there is a phi that lives in loop header depends on loop
				// def while such loop def reversely depends on phi, we need to
				// clone the whole loop def and Phi(this is different from normal
				// trivial loop def), and update cloned ones. The original phi
				// must be preserved because it may used by other values inside
				// loop, update on that value slightly changes semantic. Here is
				// a simple example:
				//
				// loop header:
				//  v1 = Phi(0, v2)
				//  v2 = Add64(v1, 1)
				//  If v2 <3 -> loop latch, loop exit
				//
				// after loop rotation:
				// loop guard:
				//  v4 = Add64(v1, 1)
				//
				// loop header:
				// 	v2 = Phi(0, v2)
				// 	...
				//
				// loop latch:
				//  v3 = Phi(<>,v2) ;; Cloned!
				// 	v2 = Add64(v1, 1)
				//  If v2 < 3 -> loop header, loop exit
				//
				narg := arg.copyIntoWithXPos(t.valBlock, arg.Pos)
				narg.SetArg(1-loopPhiIdx, isomorphic)
				val.SetArg(iarg, narg)
			}
		} else {
			t.update(arg, loopHeader, loopPhiIdx, depth+1)
		}
	}
}

func cloneTrivial(val *Value, dest *Block, loopHeader *Block, loopPhiIdx int) (*Value, map[*Value]*Value) {
	t := &loopTrivialVal{
		valBlock: val.Block,
		visited:  make(map[*Value]*Value),
	}
	clone := t.clone(val, dest, InitDepth)
	t.valBlock = dest
	t.update(clone, loopHeader, loopPhiIdx, InitDepth) // update cloned value
	return clone, t.visited
}

func moveTrivial(val *Value, dest *Block, loopHeader *Block, cloned map[*Value]*Value, loopPhiIdx int) {
	t := &loopTrivialVal{
		valBlock: val.Block,
	}
	t.move(val, dest, InitDepth)
	t.valBlock = dest
	t.visited = cloned
	t.update(val, loopHeader, loopPhiIdx, InitDepth) // update moved value
}

func isomorphic(block *Block, a, b *Value, depth int) bool {
	assert(depth < MaxDepth, "excess max search depth")
	if a == b {
		return true
	}
	if a.Op == OpPhi || b.Op == OpPhi {
		// return a.Op == b.Op && a.Type == b.Type && a.Aux == b.Aux &&
		// 	a.Block == b.Block && a.AuxInt == b.AuxInt
		return true
	}
	if a.Op != b.Op || a.Aux != b.Aux || a.Type != b.Type || a.AuxInt != b.AuxInt {
		return false
	}

	for idx, use := range a.Args {
		if !isomorphic(block, use, b.Args[idx], depth+1) {
			return false
		}
	}
	return true
}

const (
	LoopGuard2HeaderPredIdx = 0
	LoopLatch2HeaderPredIdx = 1
)

// rewireLoopHeader rewires loop header to loop body unconditionally
func (loop *loop) rewireLoopHeader(exitIdx int) {
	loopHeader := loop.header
	loopHeader.Reset(BlockPlain)

	e := loopHeader.Succs[1-exitIdx]
	// loopHeader -> loopBody(0)
	loopHeader.Succs = loopHeader.Succs[:1]
	loopHeader.Succs[0] = e
}

// rewireLoopLatch rewires loop latch to loop header and loop exit
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

// rewireLoopGuard rewires loop guard to loop header and loop exit
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

// rewireLoopEntry rewires loop entry to loop guard
func (loop *loop) rewireLoopEntry(sdom SparseTree, loopGuard *Block) {
	entry := sdom.Parent(loop.header)
	// loopEntry -> loopGuard
	entry.Succs = entry.Succs[:0]
	entry.AddEdgeTo(loopGuard)
}

// moveCond moves conditional test from loop header to loop latch
func (loop *loop) moveCond(cloned map[*Value]*Value) *Value {
	cond := loop.header.Controls[0]

	// if cond.Op == OpPhi {
	// 	// In rare case, conditional test is Phi, we can't move it to loop latch
	// 	// Instead, we just need to update its argument, which is done in updateCond
	// 	return cond, moved
	// }
	assert(cond.Op != OpPhi, "why not")
	moveTrivial(cond, loop.latch, loop.header, cloned, LoopLatch2HeaderPredIdx)
	return cond
}

// updateCond updates conditional test to use updated Phi as arguments to avoid
// losing one update
func (loop *loop) updateCond(cond *Value, loopPhiIdx int) *Value {
	// In original while/for loop, a critical edge is inserted at the end of each
	// iteration, and Phi values are updated. All subsequent uses of Phi rely on
	// the updated values. However, when converted to a do-while loop, Phi nodes
	// may be used at the end of each iteration before they are updated.
	// Therefore, we need to replace all subsequent uses of Phi with the use of
	// Phi parameter. This way, it is equivalent to using the updated values of
	// Phi values. Here is a simple example:
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
	if cond.Op == OpPhi {
		// Rare case, returns desired incoming argument instead of updating it
		//	   If (Phi v1 v2) -> loop body, loop exit
		// =>  If v1          -> loop header, loop exit
		return cond.Args[loopPhiIdx]
	} else {
		// Normal case, update as usual
		//	  If (Less v1 Phi(v2 v3)) -> loop body, loop exit
		// => If (Less v1 v2)         -> loop header, loop exit
		// updateTrivial(loop.header, cond.Block, cond, loopPhiIdx, InitDepth)
		return cond
	}
}

// splitCritical splits the critical edge from start to end and insert an empty
// block in the middle of them.
func splitCritical(fn *Func, start, end *Block) *Block {
	if len(start.Succs) < 2 || len(end.Preds) < 2 {
		fn.Fatalf("Not a critical edge from %v to %v", start, end)
	}
	empty := fn.NewBlock(BlockPlain)
	empty.Preds = make([]Edge, 1, 1)
	empty.Succs = make([]Edge, 1, 1)
	start.ReplaceSucc(end, empty, 0)
	end.ReplacePred(start, empty, 0)
	return empty
}

// Now that the loop header no longer dominates the loop exit and the loop exit
// has an extra edge from the loop guard to it, the loop closed phi in all loop
// exits needs new arguments to reflect this new edge.
// Also to avoid losing an update (see updateCond), we need to update the incoming
// parameter of the loop closed phi corresponding to the edge from loop latch to
// loop exit.
// Depending on whether the loop closed phi uses the loop phi directly or indirectly
// through some other type of value, i.e., using the trivial loop def, the update
// strategy is different. For direct use, we only need to update the parameter
// corresponding to loop closed phi, for the latter, we need to clone the entire
// chain of trivial loop def and then replace the indirect use with the clone Value
func (loop *loop) updateLoopUse(fn *Func) {
	fn.invalidateCFG()
	sdom := fn.Sdom()
	loopExit := loop.exit
	var splitB1, splitB2 *Block
	// Walk the loop exit, find all loop closed phi
	for _, val := range loopExit.Values {
		if val.Op != OpPhi {
			continue
		}
		assert(len(val.Args) == len(loopExit.Preds)-1, "less than loop exit preds %v", val)

		mergeArgs := make([]*Value, len(loopExit.Preds))
		var g2eArg *Value // new guard to exit path

		// Visit all arguments of the loop closed phi
		for iarg, arg := range val.Args {
			mergeArgs[iarg] = arg
			exitPred := loopExit.Preds[iarg].b
			// If incoming argument of loop closed phi reflects the edge of
			// loop latch to loop exit, then update it
			if loop.latch == exitPred || splitB1 == exitPred {
				// If arg strictly dominates loop header, use it directly
				if sdom.isAncestor(arg.Block, loop.header) {
					g2eArg = arg
				} else if arg.Block == loop.header {
					guardIdx := 0
					if loop.header.Preds[0].b == loop.latch {
						guardIdx = 1 // then index 1 is loop guard
					}
					backedgeIdx := 1 - guardIdx

					if arg.Op != OpPhi {
						found := false
						// for _, v := range loop.latch.Values {
						// 	if isomorphic(loop.latch, v, arg, 0) {
						// 		fmt.Printf("@@F1%v %v ##%v\n", v.LongString(), arg.LongString(), fn.Name)
						// 		mergeArgs[iarg] = v
						// 		found = true
						// 		break
						// 	} else {
						// 		fmt.Printf("Diff1%v/%v\n", v.LongString(), arg.LongString())
						// 	}
						// }
						if !found {
							if splitB1 == nil {
								splitB1 = splitCritical(fn, loop.latch, loop.exit)
							}
							backedgeArg, _ := cloneTrivial(arg, splitB1, loop.header, backedgeIdx)
							// updateTrivial(loop.header, splitB1, backedgeArg, backedgeIdx, 0)
							mergeArgs[iarg] = backedgeArg
						}
						found = false
						// for _, v := range loop.guard.Values {
						// 	if isomorphic(loop.guard, v, arg, 0) {
						// 		fmt.Printf("@@F1%v %v ##%v\n", v.LongString(), arg.LongString(), fn.Name)
						// 		g2eArg = v
						// 		found = true
						// 		break
						// 	} else {
						// 		fmt.Printf("Diff2%v/%v\n", v.LongString(), arg.LongString())
						// 	}
						// }
						if !found {
							if splitB2 == nil {
								splitB2 = splitCritical(fn, loop.guard, loop.exit)
							}
							guardArg, _ := cloneTrivial(arg, splitB2, loop.header, guardIdx)
							// updateTrivial(loop.header, splitB2, guardArg, guardIdx, 0)
							g2eArg = guardArg
						}
					} else {
						backedgeArg := arg.Args[backedgeIdx]
						guardArg := arg.Args[guardIdx]
						mergeArgs[iarg] = backedgeArg
						g2eArg = guardArg
					}
				} else {
					// Otherwise it's insane, die
					fn.Fatalf("loop def %v(%v) is incorrectly used by %v",
						arg, loop.LongString(), val.LongString())
				}
			}
		}

		// Update old loop closed phi arguments right now
		if g2eArg != nil {
			fmt.Printf("Update %v\n", val.LongString())
			mergeArgs[len(loop.exit.Preds)-1] = g2eArg
			val.resetArgs()
			val.AddArgs(mergeArgs...)
		} else {
			fn.Fatalf("Can not determine new arg of Phi for guard to exit path")
		}
	}
}

func (loop *loop) updateMovedValues(fn *Func, ln *loopnest, cloned map[*Value]*Value) {
	// Find all moved values
	moved := make([]*Value, 0)
	for key, _ := range cloned {
		moved = append(moved, key)
	}
	sort.SliceStable(moved, func(i, j int) bool {
		return moved[i].ID < moved[j].ID
	})
	// For each of moved value, find its uses inside loop, and replace them with
	// inserted Phi
	replacement := make(map[*Value]*Value)
	defUses := buildDefUses(fn, moved)
	for _, def := range moved {
		// if def.Uses == 1 {
		// 	continue
		// }
		uses := defUses[def]
		fmt.Printf("++Moved%v %v\n", def, uses)
		for _, use := range uses {
			// If use is one of the moved values, no need to update
			// useBlock := use.useBlock()
			if use.val != nil {
				if _, exist := cloned[use.val]; exist {
					continue
				}
				if use.val.Op == OpPhi && use.val.Block == loop.header {
					continue
				}
			} else {
				if _, exist := cloned[use.block.ControlValues()[0]]; exist {
					continue
				}
			}
			// Since LCSSA ensures that all uses of loop defined values are in loop
			// if ln.b2l[useBlock.ID] == loop || ln.containsBlock(loop, useBlock) {
			// Create phi at loop header, merge control flow from loop guard and
			// loop latch, and replace use with such phi. If phi already exists,
			// use it instead of creating a new one.
			val := def
			if d, exist := replacement[def]; exist {
				val = d
			} else {
				phi := fn.newValueNoBlock(OpPhi, def.Type, def.Pos)
				phiArgs := make([]*Value, 2)
				assert(cloned[def].Block == loop.guard, "cloned guy must be live in loop guard")
				phiArgs[0] = cloned[def] // find cloned vlaue from loop guard
				assert(def.Block == loop.latch, "def must be live in loop latch")
				phiArgs[1] = def
				phi.AddArgs(phiArgs...)
				loop.header.placeValue(phi)
				fmt.Printf("++Insert %v %v\n", phi.LongString(), use)
				replacement[def] = phi
				val = phi
			}
			use.replaceUse(val)
			// } else {
			// TODO: CHECK ONLY WHEN PASS.DEBUG > 1
			// found := false
			// for _, exit := range loop.exits {
			// 	if exit == useBlock {
			// 		found = true
			// 		break
			// 	}
			// }
			// assert(found, "use block not in loop %v %v %v %v", loop.LongString(), def.LongString(), use, useBlock)
			// }
		}
	}
}

// verifyRotatedForm verifies if given loop is rotated form
func (loop *loop) verifyRotatedForm(fn *Func) {
	if len(loop.header.Succs) != 1 || len(loop.exit.Preds) < 2 ||
		len(loop.latch.Succs) != 2 || len(loop.guard.Succs) != 2 {
		fn.Fatalf("Bad loop %v after rotation", loop.LongString())
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

func loopRotate(f *Func) {
	loopnest := f.loopnest()
	if loopnest.hasIrreducible || len(loopnest.loops) == 0 {
		return
	}

	for _, loop := range loopnest.loops {
		f.RotateLoop(loop)
	}
}

// TODO: 新增测试用例
// TODO: 压力测试，在每个pass之后都执行loop rotate；执行多次loop rotate；打开ssacheck；确保无bug
// 33064/36000 rotated/bad before lower
// 39022/25245 rotated/bad before lower, lcssa
// 46986/17281 rotated/bad before lower, lcssa
// 47053/17162 rotated/bad before lower, lcssa with arbitary exit order
// 52236/12282 rotated/bad before lower, allow multiple preds of exit
// 53101/12278 rotated/bad loop exit belongs to current loop
// 55467/13124 bad/rotated lcssa allow multiple prede
// 59690/7950 rotated/exotic clone cond instead
// RotateLoop rotates the original loop to become a do-while style loop, it returns
// true if loop is rotated, false otherwise.
func (fn *Func) RotateLoop(loop *loop) bool {
	if loop.IsRotatedForm() {
		return true
	}
	// if fn.Name != "NewName" {
	// 	return false
	// }
	// if fn.Name != "(*regAllocState).liveAfterCurrentInstruction" {
	// 	return false
	// }
	// if fn.Name != "heapBitsSetType" {
	// 	return false
	// }
	// Try to build loop form and bail out if failure
	if msg := loop.checkLoopForm(fn); msg != "" {
		// if fn.pass.debug > 1 {
		fmt.Printf("Exotic %v for rotation: %s %v\n", loop.LongString(), msg, fn.Name)
		// }
		return false
	}

	ln := fn.loopnest()
	// fmt.Printf("==before%v\n", fn.String())

	exitIdx := 1 // which successor of loop header wires to loop exit
	if loop.header.Succs[0].b == loop.exit {
		exitIdx = 0
	}
	assert(len(loop.header.ControlValues()) == 1, "more than 1 ctrl values")
	cond := loop.header.Controls[0]

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
	guardCond, cloned := cloneTrivial(cond, loop.guard, loop.header, LoopGuard2HeaderPredIdx)
	// guardCond = loop.updateCond(guardCond, LoopGuard2HeaderPredIdx)

	// Rewire loop guard to original loop header and loop exit
	loop.rewireLoopGuard(fn.Sdom(), guardCond, exitIdx)

	// CFG changes are done, then update data dependencies accordingly
	// Update cond to use updated Phi as arguments
	// Move conditional test from loop header to loop latch
	// loop.moveCond()
	// loop.updateCond(cond, LoopLatch2HeaderPredIdx)
	moveTrivial(cond, loop.latch, loop.header, cloned, LoopLatch2HeaderPredIdx)

	// Update chain of the moved Values
	loop.updateMovedValues(fn, ln, cloned)

	// Update loop uses as loop header no longer dominates exit
	loop.updateLoopUse(fn)

	// Gosh, loop is rotated
	loop.verifyRotatedForm(fn)

	// if fn.pass.debug > 1 {
	fmt.Printf("%v rotated in %v\n", loop.LongString(), fn.Name)
	// }
	fn.invalidateCFG()
	// fmt.Printf("==after%v\n", fn.String())
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
