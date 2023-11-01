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
// equal to loop latch, and loop exit refers to the block that dominated by the
// entire loop.
// We move the conditional test from loop header to loop latch, incoming backedge
// argument of conditional test should be updated as well otherwise we would lose
// one update. Also note that any other uses of moved values should be updated
// because moved Values now live in loop latch and may no longer dominates their
// uses. At this point, loop latch determines whether loop continues or exits
// based on rotated test.
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
//     * Rewire loop header to loop body unconditionally.
//     * Rewire loop latch to header and exit based on new conditional test.
//     * Create new loop guard block and rewire loop entry to loop guard.
//     * Clone conditional test from loop header to loop guard.
//     * Rewire loop guard to original loop header and loop exit
//
//  3. Update data dependencies after CFG transformation
//     * Move conditional test from loop header to loop latch
//     * Update uses of moved Values because these defs no longer dominates uses
//       after they were moved to loop latch
//     * Update loop uses as loop header no longer dominates exit

// checkLoopForm checks if loop is well formed and returns failure reason if not
func (loop *loop) checkLoopForm(fn *Func, sdom SparseTree) string {
	loopHeader := loop.header
	// Check if loop header is well formed block
	if len(loopHeader.Preds) != 2 || len(loopHeader.Succs) != 2 ||
		loopHeader.Kind != BlockIf {
		return "illegal loop header"
	}

	// Check if loop exit nears the loop header
	fn.loopnest().findExits() // initialize loop exits
	e1, e2 := loopHeader.Succs[1].b, loopHeader.Succs[0].b
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

	// Check loop conditional test is "trivial"
	for _, ctrl := range loop.header.ControlValues() {
		if !loop.isTrivial(sdom, ctrl, true) {
			return "non trivial loop cond"
		}
	}

	// Check if all loop uses are "trivial"
	for ipred, pred := range loop.exit.Preds {
		if pred.b == loop.header {
			for _, val := range loop.exit.Values {
				// TODO: Relax or remove this restriction
				if val.Op == OpPhi {
					if arg := val.Args[ipred]; arg.Block == loop.header {
						if !loop.isTrivial(sdom, arg, false) {
							return "use non trivial loop def outside loop"
						}
					}
				} else if val.Block == loop.header {
					if !loop.isTrivial(sdom, val, false) {
						return "use non trivial loop def outside loop"
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
	cloning  bool
	valBlock *Block
	touched  map[*Value]*Value
}

func (t *loopTrivialVal) clone(val *Value, dest *Block, depth int) *Value {
	// If seeing Phi or value that lives different from source block? They must
	// not part of trivial loop def chain, do nothing
	if val.Op == OpPhi || val.Block != t.valBlock {
		return val
	}
	// If val is already cloned? Use cloned value instead.
	if c, exist := t.touched[val]; exist {
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
	t.touched[val] = clone // cache cloned value after cloning its arguments
	return clone
}

func (t *loopTrivialVal) move(val *Value, dest *Block, depth int) {
	if val.Op == OpPhi || val.Block != t.valBlock {
		return
	}
	for _, arg := range val.Args {
		t.move(arg, dest, depth+1)
	}
	moveTo(val, dest)
}

func (t *loopTrivialVal) update(val *Value, loop *loop, loopPhiIdx, depth int) {
	if val.Op == OpPhi || val.Block != t.valBlock {
		return
	}
	for iarg, arg := range val.Args {
		// If arg of val is a Phi which lives in loop header?
		if arg.Op == OpPhi && arg.Block == loop.header {
			// If expected incoming argument of arg is not visited yet, this implies
			// that it may comes from loop latch, this is the most common case,
			// update val to use incoming argument instead of arg. Otherwise,
			// there is a cyclic dependencies, see below for more details.
			newUse := arg.Args[loopPhiIdx]
			if _, livesInHeader := t.touched[newUse]; !livesInHeader {
				// In original while/for loop, a critical edge is inserted at the
				// end of each iteration, and Phi values are updated. All subsequent
				// uses of Phi rely on the updated values. However, when converted
				// to a do-while loop, Phi nodes may be used at the end of each
				// iteration before they are updated. Therefore, we need to replace
				// all subsequent uses of Phi with the use of Phi parameter. This
				// way, it is equivalent to using the updated values of Phi values.
				// Here is a simple example:
				//
				// Normal case, if v2 uses v1 phi, and the backedge operand v4
				// of v1 phi is located in the loop latch block, we only need to
				// modify the usage of v1 by v2 to the usage of v4. This prevents
				// loss of updates, and the dominance relationship will not be
				// broken even after v2 is moved to the loop latch.
				//
				// Before:
				//  loop header:
				//  v1 = phi(0, v4)
				//  v2 = v1 +1
				//  If v2 < 3 -> loop body, loop exit
				//
				//  loop latch:
				//  v4 = ...
				//
				// After:
				//  loop header:
				//  v1 = phi(0, v4)
				//
				//  loop latch:
				//  v4 = ...
				//  v2 = v4 +1
				//  If v2 < 3 -> loop header, loop exit
				val.SetArg(iarg, newUse)
			} else {
				// If there is a value v1 in the loop header that is used to define
				// a v2 phi in the same basic block, and this v2 phi is used in
				// turn to use the value v1, there is a cyclic dependencies, i.e.
				//
				//  loop header:
				//  v1 = phi(0, v2)
				//  v2 = v1 + 1
				//  If v2 < 3 -> loop body, loop exit
				//
				// In this case, we need to first convert the v1 phi into its
				// normal form, where its back edge parameter uses the value defined
				// in the loop latch.
				//
				//  loop header:
				//  v1 = phi(0, v3)
				//  v2 = v1 + 1
				//  If v2 < 3 -> loop body, loop exit
				//
				//  loop latch:
				//  v3 = Copy v2
				//
				// After this, the strange v1 phi is treated in the same way as
				// other phis. After moving the conditional test to the loop latch,
				// the relevant parameters will also be updated, i.e., v2 will
				// use v3 instead of v1 phi:
				//
				//  loop header:
				//  v1 = phi(0, v3)
				//
				//  loop latch:
				//  v3 = Copy v2
				//  v2 = v3 + 1
				//  If v2 < 3 -> loop header, loop exit
				//
				// Finally, since v3 is use of v2, after moving v2 to the loop
				// latch, updateMovedUses will update these uses and insert a
				// new v4 Phi.
				//
				//  loop header:
				//  v1 = phi(0, v3)
				//  v4 = phi(v2', v2)    ;;; v2' lives in loop guard
				//
				//  loop latch:
				//  v3 = Copy v4
				//  v2 = v3 + 1
				//  If v2 < 3 -> loop header, loop exit

				// Copy from cyclic dependency value and place it to loop latch
				fn := arg.Block.Func
				copy := fn.newValueNoBlock(OpCopy, arg.Type, arg.Pos)
				if t.cloning {
					// If we are cloning, we need to be very careful when updating
					// the clonee, not the clone, otherwise, it can lead to another
					// disastrous circular dependencies, e.g.
					//
					//  loop header:
					//  v1 = phi(0, v3)
					//
					//  loop latch:
					//  v3 = Copy v2
					//  v2 = v3 + 1
					//  If v2 < 3 -> loop header, loop exit
					//
					//  critical block(between loop latch and loop exit):
					//  v3' = Copy v2    ;;; copy from v2 instead of v2'
					//  v2' = v3' + 1
					for clonee, clone := range t.touched {
						if clone == val {
							copy.SetArgs1(clonee)
							break
						}
					}
					if len(copy.Args) == 0 {
						fn.Fatalf("can not found clone from clonee")
					}
				} else {
					copy.SetArgs1(newUse)
				}
				loop.latch.placeValue(copy)
				// Replace incoming argument of loop phi to copied value
				arg.SetArg(loopPhiIdx, copy)
				// Update val to use copied value as usual
				val.SetArg(iarg, copy)

				if fn.pass.debug > 1 {
					fmt.Printf("== Insert %v during updating %v\n", copy, val)
				}
			}
		} else {
			t.update(arg, loop, loopPhiIdx, depth+1)
		}
	}
}

func (t *loopTrivialVal) valid(sdom SparseTree, val *Value, allowSideEffect bool, depth int) bool {
	if depth >= MaxDepth {
		return false
	}

	if sdom.isAncestor(val.Block, t.valBlock) {
		return true
	}

	if val.Op == OpPhi {
		if val.Block == t.valBlock {
			return true
		}
		return false
	}

	if !allowSideEffect {
		if val.Op != OpLoad && isAccessMemory(val) {
			return false
		}
	}
	for _, arg := range val.Args {
		if !t.valid(sdom, arg, allowSideEffect, depth+1) {
			return false
		}
	}
	return true
}

// isTrivial checks if val is "trivial" and returns true if it is, otherwise false.
func (loop *loop) isTrivial(sdom SparseTree, val *Value, allowSideEffect bool) bool {
	t := &loopTrivialVal{
		valBlock: loop.header,
	}
	return t.valid(sdom, val, allowSideEffect, InitDepth)
}

// cloneTrivial clones val to destination block and updates its uses accordingly
func (loop *loop) cloneTrivial(val *Value, dest *Block, loopPhiIdx int) (*Value, map[*Value]*Value) {
	t := &loopTrivialVal{
		cloning:  true,
		valBlock: val.Block,
		touched:  make(map[*Value]*Value),
	}
	clone := t.clone(val, dest, InitDepth)
	t.valBlock = dest
	t.update(clone, loop, loopPhiIdx, InitDepth) // update cloned value
	return clone, t.touched
}

// moveTrivial moves val to destination block and updates its uses accordingly
func (loop *loop) moveTrivial(val *Value, dest *Block, cloned map[*Value]*Value, loopPhiIdx int) {
	t := &loopTrivialVal{
		cloning:  false,
		valBlock: val.Block,
	}
	t.move(val, dest, InitDepth)
	t.valBlock = dest
	t.touched = cloned
	t.update(val, loop, loopPhiIdx, InitDepth) // update moved value
}

// moveCond moves conditional test from loop header to loop latch
func (loop *loop) moveCond(cond *Value, cloned map[*Value]*Value) {
	if cond.Block != loop.header {
		// More rare, ctrl Value is not live in loop header, do nothing
		return
	}

	if cond.Op == OpPhi {
		// Rare case, Phi is used as conditional test, use its incoming argument
		//     If (Phi v1 v2) -> loop body, loop exit
		// =>  If v1          -> loop header, loop exit
		cond = cond.Args[LoopLatch2HeaderPredIdx]
		loop.latch.SetControl(cond)
		return
	}

	// Normal case, update as usual
	//    If (Less v1 Phi(v2 v3)) -> loop body, loop exit
	// => If (Less v1 v2)         -> loop header, loop exit
	loop.moveTrivial(cond, loop.latch, cloned, LoopLatch2HeaderPredIdx)
}

// cloneCond clones conditional test from loop header to loop guard
func (loop *loop) cloneCond(cond *Value) (*Value, map[*Value]*Value) {
	if cond.Block != loop.header {
		return cond, nil
	}

	if cond.Op == OpPhi {
		guardCond := cond.Args[LoopGuard2HeaderPredIdx]
		return guardCond, nil
	}

	return loop.cloneTrivial(cond, loop.guard, LoopGuard2HeaderPredIdx)
}

const (
	LoopGuard2HeaderPredIdx = 0
	LoopLatch2HeaderPredIdx = 1
)

// rewireLoopHeader rewires loop header to loop body unconditionally
func (loop *loop) rewireLoopHeader() {
	loopHeader := loop.header
	loopHeader.Reset(BlockPlain)

	// loopHeader -> loopBody(0)
	loopHeader.Succs = loopHeader.Succs[:1]
	loopHeader.Succs[0] = Edge{loop.body, 0}
	assert(len(loop.body.Preds) == 1, "why not otherwise")
	loop.body.Preds[0] = Edge{loopHeader, 0}
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
		// loopLatch -> loopHeader(0), loopExit(1)
		loopLatch.Succs = append(loopLatch.Succs, Edge{loopExit, idx})
	} else {
		// loopLatch -> loopExit(0), loopHeader(1)
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
func (loop *loop) rewireLoopGuard(guardCond *Value, exitIdx int) {
	loopHeader := loop.header
	loopGuard := loop.guard
	loopExit := loop.exit
	loopGuard.Pos = loopHeader.Pos
	loopGuard.Likely = loopHeader.Likely // respect header's branch predication
	loopGuard.SetControl(guardCond)

	var idx int
	assert(len(loopHeader.Preds) == 2, "sanity check")
	for i := 0; i < len(loopHeader.Preds); i++ {
		if loopHeader.Preds[i].b != loop.latch {
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
func (loop *loop) rewireLoopEntry(loopGuard *Block) {
	assert(len(loop.header.Preds) == 2, "sanity check")
	var entry *Block
	for _, pred := range loop.header.Preds {
		if pred.b != loop.latch {
			entry = pred.b
			break
		}
	}

	// loopEntry -> loopGuard
	entry.Succs = entry.Succs[:0]
	entry.AddEdgeTo(loopGuard)
}

// insertBetween inserts an empty block in the middle of start and end block.
// If such block already exists, it will be returned instead.
func insertBetween(fn *Func, start, end *Block) *Block {
	for _, succ := range start.Succs {
		if succ.b == end {
			break
		} else if succ.b.Succs[0].b == end {
			return succ.b
		}
	}
	empty := fn.NewBlock(BlockPlain)
	empty.Preds = make([]Edge, 1, 1)
	empty.Succs = make([]Edge, 1, 1)
	start.ReplaceSucc(end, empty, 0)
	end.ReplacePred(start, empty, 0)
	return empty
}

// See if loop def no longer dominates arguments of such proxy phi and update it
func (loop *loop) updateProxyPhi(sdom SparseTree, val *Value) {
	// Walk the loop exit, find all loop closed phi
	loopExit := val.Block
	isMainLoopExit := loopExit == loop.exit
	fn := val.Block.Func
	mergeArgs := make([]*Value, len(loopExit.Preds))
	copy(mergeArgs, val.Args)
	var g2eArg *Value // which reflects the path from loop guard to exit
	sdom = fn.Sdom()

	// Visit all arguments of the loop closed phi
	for iarg, arg := range val.Args {
		exitPred := loopExit.Preds[iarg].b
		// If loop header still dominate predecessor of this loop exit or this
		// predecessor is the loop latch?
		if (isMainLoopExit && sdom.IsAncestorEq(loop.latch, exitPred)) ||
			(!isMainLoopExit && sdom.isAncestor(loop.header, exitPred)) {
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
					holderB1 := insertBetween(fn, exitPred, loopExit)
					backedgeArg, _ := loop.cloneTrivial(arg, holderB1, backedgeIdx)
					mergeArgs[iarg] = backedgeArg
					if isMainLoopExit {
						holderB2 := insertBetween(fn, loop.guard, loop.exit)
						guardArg, _ := loop.cloneTrivial(arg, holderB2, guardIdx)
						g2eArg = guardArg
					}
				} else {
					backedgeArg := arg.Args[backedgeIdx]
					mergeArgs[iarg] = backedgeArg
					if isMainLoopExit {
						guardArg := arg.Args[guardIdx]
						g2eArg = guardArg
					}
				}
			} else {
				// Otherwise it's insane
				fn.Fatalf("loop def %v(%v) is incorrectly used by %v",
					arg, loop.LongString(), val.LongString())
			}
			break
		}
	}

	// Update old loop closed phi arguments right now
	if isMainLoopExit {
		if g2eArg == nil {
			fn.Fatalf("Can not determine new arg of Phi for guard to exit path")
		}
		mergeArgs[len(mergeArgs)-1] = g2eArg
	}
	oldValStr := val.LongString()
	val.resetArgs()
	val.AddArgs(mergeArgs...)
	// if fn.pass.debug > 1 {
	fmt.Printf("== Update loop use %s to %v %v\n", oldValStr, val.LongString(), val.Block.Preds)
	// }
}

// Now that the loop header no longer dominates the loop exit and the loop exit
// has an extra edge from the loop guard to it, the loop closed phi in all loop
// exits needs new arguments to reflect this new edge. Also to avoid losing an
// update (see update of trivial loop val), we need to update the incoming parameter
// of the loop closed phi corresponding to the edge from loop latch to loop exit.
// Depending on whether the loop closed phi uses the loop phi directly or indirectly
// through some other type of value, i.e., using the trivial loop def, the update
// strategy is different. For direct use, we only need to update the parameter
// corresponding to loop closed phi, for the latter, we need to clone the entire
// chain of trivial loop def and then replace the indirect use with the clone Value
func (loop *loop) updateLoopUse(fn *Func) {
	fn.invalidateCFG()
	sdom := fn.Sdom()
	visited := make(map[*Block]bool) // in case of duplciated loop exit
	for _, loopExit := range loop.exits {
		if _, exist := visited[loopExit]; exist {
			continue
		}
		// The loop exit is still dominated by loop header, no need to update
		if sdom.isAncestor(loop.header, loopExit) {
			continue
		}
		// Walk the loop exit, find all loop closed proxy phi
		for _, val := range loopExit.Values {
			if val.Op != OpPhi {
				continue
			}
			loop.updateProxyPhi(sdom, val)
		}
		visited[loopExit] = true
	}
}

// If the looop conditional test is "trivial", we will move the chain of this
// conditional test values to the loop latch, after that, they are not dominating
// the in-loop uses anymore:
//
//	loop header
//	v1 = phi(0, v3)
//	v2 = v1 + 1
//	If v2 < 3 ...
//
//	loop body:
//	v4 = v2 - 1
//
// So we need to create a new phi at the loop header to merge the control flow
// from the loop guard to the loop header and the loop latch to the loop header
// and use this phi to replace the in-loop use. e.g.
//
//	loop header:
//	v1 = phi(0, v3)
//	v4 = phi(v2', v2)     ;;; v2' lives in loop guard
//
//	loop body:
//	v3 = v4 - 1
//
//	loop latch:
//	v2 = v1 + 1
//	If v2 < 3 ...
func (loop *loop) updateMovedUses(fn *Func, cloned map[*Value]*Value) {
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
		uses := defUses[def]
		if def.Uses == 1 {
			assert(uses[0].useBlock() == loop.latch, "used by another moved val")
			continue
		}
		for _, use := range uses {
			// If use is one of the moved values or use is loop phi in loop header
			// skip them as they are not needed to update
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
			// we can safely do replacement then
			// TODO: Add verification here to check if it does lives inside loop

			// Create phi at loop header, merge control flow from loop guard and
			// loop latch, and replace use with such phi. If phi already exists,
			// use it instead of creating a new one.
			var newUse *Value
			if d, exist := replacement[def]; exist {
				assert(d.Op == OpPhi, "sanity check")
				newUse = d
			} else {
				phi := fn.newValueNoBlock(OpPhi, def.Type, def.Pos)
				arg1 := cloned[def]
				arg2 := def
				assert(arg1.Block == loop.guard, "cloned must be live in loop guard")
				assert(arg2.Block == loop.latch, "def must be live in loop latch")
				phi.AddArg2(arg1, arg2)
				loop.header.placeValue(phi)
				replacement[def] = phi
				newUse = phi
			}
			if fn.pass.debug > 1 {
				fmt.Printf("== Update moved use %v %v\n", use, newUse.LongString())
			}
			use.replaceUse(newUse)
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

// RotateLoop rotates the original loop to become a do-while style loop, it returns
// true if loop is rotated, false otherwise.
func (fn *Func) RotateLoop(loop *loop) bool {
	if loop.IsRotatedForm() {
		return true
	}

	// Check loop form and bail out if failure
	sdom := fn.Sdom()
	if msg := loop.checkLoopForm(fn, sdom); msg != "" {
		if fn.pass.debug > 0 {
			fmt.Printf("Exotic %v for rotation: %s %v\n", loop.LongString(), msg, fn.Name)
		}
		return false
	}

	exitIdx := 1 // which successor of loop header wires to loop exit
	if loop.header.Succs[0].b == loop.exit {
		exitIdx = 0
	}

	assert(len(loop.header.ControlValues()) == 1, "more than 1 ctrl values")
	cond := loop.header.Controls[0]

	// Rewire loop header to loop body unconditionally
	loop.rewireLoopHeader()

	// Rewire loop latch to header and exit based on new conditional test
	loop.rewireLoopLatch(cond, exitIdx)

	// Create loop guard block
	// TODO(yyang): Creation of loop guard can be skipped if original IR already
	// exists such form. e.g. if 0 < len(b) { for i := 0; i < len(b); i++ {...} }
	loopGuard := fn.NewBlock(BlockIf)
	loop.guard = loopGuard

	// Rewire entry to loop guard instead of original loop header
	loop.rewireLoopEntry(loopGuard)

	// Clone old conditional test and its arguments to control loop guard
	guardCond, cloned := loop.cloneCond(cond)

	// Rewire loop guard to original loop header and loop exit
	loop.rewireLoopGuard(guardCond, exitIdx)

	// CFG changes are all done here, then update data dependencies accordingly

	// Move conditional test from loop header to loop latch
	loop.moveCond(cond, cloned)

	// Update uses of moved Values because these defs no longer dominates uses
	// after they were moved to loop latch
	loop.updateMovedUses(fn, cloned)

	// Update loop uses as loop header no longer dominates exit
	loop.updateLoopUse(fn)

	// Gosh, loop is rotated
	loop.verifyRotatedForm(fn)

	// if fn.pass.debug > 0 {
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
