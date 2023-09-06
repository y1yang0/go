// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
	"sort"
)

// ----------------------------------------------------------------------------
// Loop Invariant Code Motion
//
// This pass hoists loop invariants to loop header or sink them into loop exits.
// The main idea behind LICM is to move loop invariant Value outside of the loop,
// so that they are only executed once, instead of being repeatedly executed with
// each iteration of the loop.
//
// In the context of LICM, we can classify all Values into two categories: those
// that can undergo speculative execution and those that cannot. Examples of the
// former include simple arithmetic operations (except for division and modulo
// which may trap execution due to / by zero), which can be freely hoisted to the
// loop entry. However, for the latter category, there are several prerequisites.
// To ensure program semantic correctness, Values must satisfy the following
// conditions in order to hoist it:
// TODO: TO WRITE

type loopInvariants struct {
	loopHeader *Block
	invariants map[*Value]bool
	loads      []*Value
	stores     []*Value
}

func printInvariant(val *Value, block *Block, domBlock *Block) {
	fmt.Printf("== Hoist %v from b%v to b%v in %v\n",
		val.String(),
		block.ID, domBlock.ID, block.Func.Name)
	fmt.Printf("  %v\n", val.LongString())
}

// For Load/Store and some special Values they sould be processed separately
// even if they are loop invariants as they may have observable memory side
// effect
func hasMemoryAlias(loads []*Value, stores []*Value, val *Value) bool {
	if val.Op == OpLoad {
		if len(stores) == 0 {
			// good, no other Store at all
			return false
		}
		// Slow path, we need a type-based alias analysis to know whether Load
		// may alias with Stores
		for _, st := range stores {
			loadPtr := val.Args[0]
			storePtr := st.Args[0]
			at := GetMemoryAlias(loadPtr, storePtr)
			fmt.Printf("==%v %v with %v in %v\n", at, loadPtr.LongString(), storePtr.LongString(), val.Block.Func.Name)
			if at != NoAlias {
				return true
			}
		}
		return false
	} else if val.Op == OpStore {
		if len(loads) == 0 && len(stores) == 1 /*itself only*/ {
			return false
		}
		for _, v := range append(stores, loads...) {
			ptr := v.Args[0]
			storePtr := val.Args[0]
			at := GetMemoryAlias(ptr, storePtr)
			fmt.Printf("==%v %v with %v in %v\n", at, ptr.LongString(), storePtr.LongString(), val.Block.Func.Name)
			if at != NoAlias {
				return true
			}
		}
		return false
	} else {
		//	fmt.Printf("==TO IMPLEMENT:%v\n", val.LongString())
	}
	return false
}

// isExecuteUnconditionally checks if Value is guaranteed to execute during loop iterations
// Otherwise, it should not be hoisted. The most common cases are invariants guarded by
// conditional expressions.
func isExecuteUnconditionally(sdom SparseTree, loop *loop, val *Value) bool {
	block := val.Block
	// Because loop header can always jump to the loop exit, all blocks
	// inside the loop are never post-dominated by any loop exit.
	// Therefore, we need to first apply loop rotation to eliminate the path
	// from the loop header to the loop exit.
	for _, exit := range loop.exits {
		if exit == loop.exit {
			if !sdom.IsAncestorEq(block, loop.latch) {
				return false
			}
			continue
		}
		if !sdom.IsAncestorEq(block, exit) {
			return false
		}
	}
	return true
}

func moveTo(val *Value, block *Block) {
	for valIdx, v := range val.Block.Values {
		if val != v {
			continue
		}
		val.moveTo(block, valIdx)
		break
	}
}

func hoist(f *Func, loop *loop, block *Block, val *Value) {
	// TODO: STore produces memory, all uses should be updated
	// If val has memory input, we need to replace it with new one after hoisting
	if arg := val.MemoryArg(); arg != nil {
		startMem := f.Cache.allocValueSlice(f.NumBlocks())
		defer f.Cache.freeValueSlice(startMem)
		endMem := f.Cache.allocValueSlice(f.NumBlocks())
		defer f.Cache.freeValueSlice(endMem)
		memState(f, startMem, endMem)
		newMem := endMem[loop.header.ID]
		val.SetArg(len(val.Args)-1, newMem)

		// If val produces memory, all its uses should be replaced with incoming
		// memory input of val
		switch val.Op {
		case OpStore, OpMove, OpZero, OpStoreWB, OpMoveWB, OpZeroWB:
			mem := arg
			for _, b := range f.Blocks {
				b.ReplaceUses(val, mem)
			}
		}
	}
	moveTo(val, block)
}

func isPinned(val *Value) bool {
	switch val.Op {
	case OpCopy:
		if val.Type.IsMemory() {
			return true
		}
	case OpPhi, OpInlMark, OpVarDef, OpVarLive, OpInvalid:
		return true
	}
	return false
}

// tryHoist hoists profitable loop invariant to block that dominates the entire loop.
// Value is considered as loop invariant if all its inputs are defined outside the loop
// or all its inputs are loop invariants. Since loop invariant will immediately moved
// to dominator block of loop, the first rule actually already implies the second rule
func tryHoist(fn *Func, loop *loop, li *loopInvariants, val *Value) bool {

	sdom := fn.Sdom()
	// arguments of val are all loop invariant, but they are not necessarily
	// hoistable due to various constraints, for example, memory alias, so
	// we try to hoist its arguments first
	for _, arg := range val.Args {
		if arg.Type.IsMemory() {
			continue
		}
		if _, exist := li.invariants[arg]; !exist {
			// must be type of memory or defiend outside loop
			if !arg.Type.IsMemory() && !sdom.IsAncestorEq(arg.Block, loop.header) {
				fmt.Printf("must define outside loop %v\n", arg.LongString())
				panic("must define outside loop")
			}
		} else {
			// If arguments of loop invariant does not dominate the loop, try to
			// hoist them first, this guarantees all uses of val dominates val itself
			if !sdom.isAncestor(arg.Block, loop.header) {
				if !tryHoist(fn, loop, li, arg) {
					return false
				}
			}
		}
	}

	if isPinned(val) {
		return false
	}

	// Hoist value to loop entry if it can be speculatively executed
	if canSpeculativelyExecuteValue(val) {
		// If arguments of value is hoisted to loop land, the value itself should
		// be hoisted to loop land
		for _, arg := range val.Args {
			if loop.guard != nil && !sdom.IsAncestorEq(arg.Block, loop.guard) {
				fmt.Printf("==Hoist1 %v to %v\n", val.LongString(), loop.land)
				hoist(fn, loop, loop.land, val)
				return true
			}
		}
		entry := sdom.Parent(loop.header)
		fmt.Printf("==Hoist1 %v to %v\n", val.LongString(), entry)
		hoist(fn, loop, entry, val)
		return true
	}

	// Dont worry, even if value can not be speculatively executed, there are
	// still opportunities to hoist them under few prerequisites
	if loop.IsRotatedForm() {
		// Instructions may access same memory locations?
		if hasMemoryAlias(li.loads, li.stores, val) {
			fmt.Printf("==has mem alias%v\n", val)
			return false
		}

		// Instructions are guaranteed to execute unconditionally?
		if !isExecuteUnconditionally(sdom, loop, val) {
			fmt.Printf("==not execute unconditional%v\n", val.LongString())
			return false
		}

		// Hoist value to loop land if it cannt be speculatively executed
		fmt.Printf("==Hoist2 %v to %v\n", val.LongString(), loop.land)
		hoist(fn, loop, loop.land, val)
		return true
	}

	return false
}

func findInvariant(ln *loopnest, loop *loop) *loopInvariants {
	loopValues := make(map[*Value]bool)
	invariants := make(map[*Value]bool)
	loopBlocks := ln.findLoopBlocks(loop)

	loads := make([]*Value, 0)
	stores := make([]*Value, 0)
	// First, collect all def inside loop
	for _, block := range loopBlocks {
		for _, val := range block.Values {
			loopValues[val] = true
		}
	}

	for _, block := range loopBlocks {
		// If basic block is located in a nested loop rather than directly in the
		// current loop, it will not be processed.
		if ln.b2l[block.ID] != loop {
			continue
		}

		for _, value := range block.Values {
			if value.Op == OpLoad {
				loads = append(loads, value)
			} else if value.Op == OpStore {
				stores = append(stores, value)
			} else if value.Op.IsCall() {
				// bail out the compilation if too complicated, for example, loop involves Calls
				// Theoretically we can hoist Call as long as it does not impose any observable
				// side effects, e.g. only reads memory or dont access memory at all, but
				// unfortunate we may run alias analysis in advance to get such facts, that
				// some what heavy for this pass at present, so we give up further motion
				// once loop blocks involve Calls
				return nil
			}

			isInvariant := true
			for _, use := range value.Args {
				if use.Type.IsMemory() && use.Op == OpPhi {
					// Store Load and other memory value depends on memory value, which is usually represented
					// as the non-loop-invariant memory value, for example, a memory Phi
					// in loops, but this is not true semantically. We need to treat these
					// kind of Store specifically as loop invariants.
					//
					//      v4, v5.... ;; loop invariant
					// 	cond:
					// 		v2 = Phi <mem> v1 v3
					//      v6 = ...
					// 	BlockIf v6 body, exit
					//
					//  body:
					//		v3 (15) = Store <mem> v4 v5 v2
					//  exit:
					// discard last memory value
					continue
				}
				if _, exist := invariants[use]; exist {
					continue
				}
				if _, exist := loopValues[use]; exist {
					isInvariant = false
					break
				}
			}
			if isInvariant {
				invariants[value] = true
			}
		}
	}
	return &loopInvariants{
		loopHeader: loop.header,
		invariants: invariants,
		loads:      loads,
		stores:     stores,
	}
}

// Hoist the loop-invariant panic check to loop land after rotation
// This simplifies CFG and allow more Value be hosited
//
//	                                               loop guard
//	                                                ╱      ╲
//	                                           loop land    ╲
//	                                              ╱          ╲
//	                                        new bound check*  ╲
//	       loop header                          ╱    ╲        ╱
//	        ╱   ▲   ╲                          ╱      ╲      ╱
//	       ╱     ╲   ╲                    loop header panic ╱
//	  bound check ╲  loop exit     =>       ╱   ▲      ____╱
//	    ╱   ╲     ╱                         ╲   ╱     ╱
//	   ╱     ╲   ╱                        loop latch ╱
//	panic   loop latch                        │     ╱
//	                                          │    ╱
//	                                        loop exit
func hoistBoundCheck(fn *Func, loop *loop, bcheck *Value) {
	if !loop.CreateLoopLand(fn) {
		return
	}
	bcheckBlock := bcheck.Block
	for bi, succ := range bcheckBlock.Succs {
		if succ.b.Kind == BlockExit {
			fmt.Printf("==Hoist3 %v\n", bcheck.LongString())
			// Rewire old bound check block to normal branch unconditionally
			normalBlock := bcheckBlock.Succs[1-bi].b
			bcheckBlock.Reset(BlockPlain)

			bcheckBlock.Succs = bcheckBlock.Succs[:1]
			for ni, pred := range normalBlock.Preds {
				if pred.b == bcheckBlock {
					bcheckBlock.Succs[0] = Edge{normalBlock, ni}
					break
				}
			}

			// Place new bound check between loop land and loop header
			// more than one bound chekc might be hoited so we use predecessor of loop header instead of loop land
			panicBlock := succ.b
			tail := loop.header
			head := tail.Preds[0].b
			if head == loop.guard {
				panic("where is your loop land")
			}
			block := fn.NewBlock(BlockIf)
			block.Likely = bcheckBlock.Likely
			block.Pos = bcheckBlock.Pos
			moveTo(bcheck, block)
			block.SetControl(bcheck)
			block.Preds = make([]Edge, 1, 1)
			block.Succs = make([]Edge, 2, 2)

			head.ReplaceSucc(tail, block, 0)

			for ti, tpred := range tail.Preds {
				if tpred.b == head {
					tail.ReplacePred(head, block, ti)
				}
			}
			panicBlock.ReplacePred(bcheckBlock, block, bi)
			break
		}
	}
}

// licm stands for Loop Invariant Code Motion, it hoists expressions that computes
// the same value while has no effect outside loop
func licm(f *Func) {
	if f.Name != "(*ssafn).AllocFrame" {
		return
	}

	loopnest := f.loopnest()
	if loopnest.hasIrreducible || len(loopnest.loops) == 0 {
		return
	}

	b2li := make(map[ID]*loopInvariants)

	// First, rotate all loops, this gives opportunity to simplify CFG
	for _, loop := range loopnest.loops {
		if f.RotateLoop(loop) {
			if !loop.CreateLoopLand(f) {
				f.Fatalf("Can not create loop land for %v", loop.LongString())
			}
		}

		li := findInvariant(loopnest, loop)
		if li == nil {
			continue
		}
		b2li[loop.header.ID] = li

		// Simplify CFG by hoisting bound check as much as possible
		for val, _ := range li.invariants {
			if val.Block.Kind != BlockIf ||
				(val.Op != OpIsInBounds && val.Op != OpIsSliceInBounds &&
					val.Op != OpIsNonNil /*Really?*/) {
				continue
			}
			for _, succ := range val.Block.Succs {
				b := succ.b
				if b.Kind == BlockExit && len(b.Values) == 1 {
					bvop := b.Values[0].Op
					if bvop != OpPanicBounds && bvop != OpPanicExtend {
						panic("must be panic call")
					}
					hoistBoundCheck(f, loop, val)
				}
			}
		}
	}

	// Loop exist may be hoisted, rebuild the whole loopnest here
	oldLoops := loopnest.loops
	loopnest = loopnestfor(f)
	loopnest.findExits() // isExecuteUnconditionally relies on this
	// TODO: O(N^2)
	for _, loop := range loopnest.loops {
		for _, loopx := range oldLoops {
			if loopx.header == loop.header {
				loop.exit = loopx.exit
				loop.guard = loopx.guard
				loop.latch = loopx.latch
				loop.body = loopx.body
				loop.land = loopx.land
				break
			}
		}
	}
	// Compute def-use chains for values that can produce memory
	// v3 = const v1 v2
	// v4 = load v3
	defUses := make(map[*Value][]*Value)
	for _, block := range f.Blocks {
		for _, val := range block.Values {
			defUses[val] = make([]*Value, 0, val.Uses)
			for _, arg := range val.Args {
				if defUses[val]
			}
		}
	}

	// At this point, the CFG shape is fixed, apply LICM for each loop invariants
	for id, loop := range loopnest.b2l {
		if li, exist := b2li[ID(id)]; exist {
			// To avoid compilation stale
			keys := make([]*Value, 0)
			for k, _ := range li.invariants {
				keys = append(keys, k)
			}
			sort.SliceStable(keys, func(i, j int) bool {
				return keys[i].ID < keys[j].ID
			})
			fmt.Printf("==invariants %v\n", keys)
			for _, val := range keys {
				tryHoist(f, loop, li, val)
			}
		}
	}
}
