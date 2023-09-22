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
// The main idea behind LICM is to move loop invariant values outside of
// the loop so that they are only executed once, instead of being repeatedly
// executed with each iteration of the loop. In the context of LICM, if a loop
// invariant can be speculatively executed, then it can be freely hoisted to the
// loop entry. However, if it cannot be speculatively executed, there is still a
// chance that it can be hoisted outside the loop under a few prerequisites:
//
// 	1) Instruction is guaranteed to execute unconditionally
//  2) Instruction does not access memory locations that may alias with other
//    memory operations inside the loop
//
// For 1), this is guaranteed by loop rotation, where the loop is guaranteed to
// execute at least once after rotation. But that's not the whole story. If the
// instruction is guarded by a conditional expression (e.g., loading from a memory
// address usually guarded by an IsInBound check), in this case, we try to hoist
// the whole conditional expression outside the loop and then check if the loop
// invariant dominates all loop exits (which implies that it will be executed
// unconditionally as soon as it enters the loop).
// For 2), we rely on a simple but efficient type-based alias analysis to analyze
// whether two memory access instructions may access the same memory location.

type loopInvariants struct {
	invariants map[*Value]bool
	loads      []*Value
	stores     []*Value
}

type hoister struct {
	fn         *Func
	panicExits map[*Block]bool
	sdom       SparseTree
	hoisted    map[*Value]bool
}

func (li *loopInvariants) stableKeys() []*Value {
	keys := make([]*Value, 0)
	for k, _ := range li.invariants {
		keys = append(keys, k)
	}
	sort.SliceStable(keys, func(i, j int) bool {
		return keys[i].ID < keys[j].ID
	})
	return keys
}

func printInvariant(val *Value, block *Block, domBlock *Block) {
	fmt.Printf("Hoist %v from b%v to b%v in %v\n",
		val.String(),
		block.ID, domBlock.ID, block.Func.Name)
	fmt.Printf("  %v\n", val.LongString())
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

func computeMemState(f *Func) ([]*Value, []*Value) {
	startMem := f.Cache.allocValueSlice(f.NumBlocks())
	// defer f.Cache.freeValueSlice(startMem)
	endMem := f.Cache.allocValueSlice(f.NumBlocks())
	// defer f.Cache.freeValueSlice(endMem)
	memState(f, startMem, endMem)
	return startMem, endMem
}

func isMemoryDef(val *Value) bool {
	switch val.Op {
	case OpStore, OpMove, OpZero, OpStoreWB, OpMoveWB, OpZeroWB,
		OpVarDef, OpVarLive, OpKeepAlive:
		return true
	}
	return false
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
			if at != NoAlias {
				//fmt.Printf("Alias: %v %v with %v in %v\n", at, loadPtr.LongString(), storePtr.LongString(), val.Block.Func.Name)
				return true
			}
		}
		return false
	} else if val.Op == OpStore {
		if len(loads) == 0 && len(stores) == 1 /*itself only*/ {
			return false
		}
		for _, v := range append(stores, loads...) {
			if v == val {
				continue
			}
			ptr := v.Args[0]
			storePtr := val.Args[0]
			at := GetMemoryAlias(ptr, storePtr)
			if at != NoAlias {
				//fmt.Printf("Alias: %v %v with %v in %v\n", at, ptr.LongString(), storePtr.LongString(), val.Block.Func.Name)
				return true
			}
		}
		return false
	} else {
		//	fmt.Printf("==TO IMPLEMENT:%v\n", val.LongString())
	}
	return false
}

// alwaysExecute checks if Value is guaranteed to execute during loop iterations
// Otherwise, it should not be hoisted. The most common cases are invariants
// guarded by a conditional expression.
// TODO(yyang): If we can prove that Value can speculative execute nevertheless,
// e.g. Load from non-null pointer, this is not really necessary
func alwaysExecute(sdom SparseTree, loop *loop, panicExits map[*Block]bool, val *Value) bool {
	block := val.Block
	// Because loop header can always jump to the loop exit, all blocks
	// inside the loop are never post-dominated by any loop exit.
	// Therefore, we need to first apply loop rotation to eliminate the path
	// from the loop header to the loop exit.
	for _, exit := range loop.exits {
		if _, exist := panicExits[exit]; exist {
			// Loop exists in panicExits implies they were already hoisted thus
			// no longer real loop exits, so skip them
			continue
		}
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

func isConservativeCandidate(val *Value) bool {
	assert(!isSpeculativeValue(val), "sanity check")
	if isDivMod(val.Op) || isPtrArithmetic(val.Op) {
		return true
	}

	switch val.Op {
	case OpLoad, OpStore, OpNilCheck, OpGetG, OpVarDef:
		return true
	}
	return false
}

func isHoistableBoundCheck(val *Value) bool {
	if val.Block.Kind != BlockIf ||
		(val.Op != OpIsInBounds && val.Op != OpIsSliceInBounds &&
			val.Op != OpIsNonNil /*real case?*/) {
		return false
	}
	for _, succ := range val.Block.Succs {
		b := succ.b
		if b.Kind == BlockExit {
			for _, bv := range b.Values {
				if bv.Op == OpPanicBounds || bv.Op == OpPanicExtend {
					assert(bv.Op == OpPanicBounds || bv.Op == OpPanicExtend,
						"must be panic call")
					fmt.Printf("==GOOD BC\n", b)
					// panic plus one loop close phi
					// assert(len(b.Values) <= 2, "just guess..")
					return false
				}
			}

		}
	}
	return false
}

func (h *hoister) hoist(block *Block, val *Value) {
	// TODO: STore produces memory, all uses should be updated
	// If val has memory input, we need to replace it with new one after hoisting
	if arg := val.MemoryArg(); arg != nil {
		// NOTE, memory SSA subgraph must update later.

		// If val produces memory, all its uses should be replaced with incoming
		// memory input of val
		if isMemoryDef(val) {
			mem := arg
			for _, b := range h.fn.Blocks {
				b.replaceUses(val, mem)
			}
		}
	}
	moveTo(val, block)
	h.hoisted[val] = true
}

// Hoist the loop-invariant panic check to loop land after rotation
// This simplifies CFG and allows more Values be hosited
//
//	                                               loop guard
//	                                                ╱     ╲
//	                                           loop land   ╲
//	                                             ╱          ╲
//	       loop header                      new bound check* ╲
//	        ╱   ▲   ╲                          ╱      ╲      ╱
//	       ╱     ╲   ╲                    loop header panic ╱
//	  bound check ╲  loop exit     =>       ╱   ▲      ____╱
//	    ╱   ╲     ╱                         ╲   ╱     ╱
//	   ╱     ╲   ╱                        loop latch ╱
//	panic   loop latch                        │     ╱
//	                                          │    ╱
//	                                        loop exit
func (h *hoister) hoistBoundCheck(loop *loop, bcheck *Value) {
	var panicExit *Block
	bcheckBlock := bcheck.Block
	for bi, succ := range bcheckBlock.Succs {
		if succ.b.Kind == BlockExit {
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
			// more than one bound chekc might be hoited so we use predecessor
			// of loop header instead of loop land
			panicBlock := succ.b
			panicExit = panicBlock
			tail := loop.header
			head := tail.Preds[0].b
			assert(head != loop.guard, "where is your loop land")
			block := h.fn.NewBlock(BlockIf)
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
	h.panicExits[panicExit] = true
	h.hoisted[bcheck] = true
}

// tryHoist hoists profitable loop invariant to block that dominates the entire loop.
// Value is considered as loop invariant if all its inputs are defined outside the loop
// or all its inputs are loop invariants. Since loop invariant will immediately moved
// to dominator block of loop, the first rule actually already implies the second rule
//
// baseline complex 3746, simple 69389, bound check 89
// v1       complex 3801, simple 8795, bound check 23
// v2       complex 4364, simple 8839, bound check 23
// v3(getg) complex 4399, simple 8839, bound check 23
// complex 4600, store16, load1897, vardef201,getg7, check23     ::v4 vardef
// merged  4484, store16, load1866, nilcheck 519, boundcheck23
// all     5803, store19, load2451, nilcheck 661, boundcheckNaN  use lcssa
// all     5874, store19, load2476, nilcheck 661, boundcheckNaN  use lcssa
// all     6951, store34, load2910, nilcheck 870, boundcheckNan  allow multiple preds of exit
func (h *hoister) tryHoist(loop *loop, li *loopInvariants, val *Value) bool {
	if hoisted, exist := h.hoisted[val]; exist {
		return hoisted
	}

	// Try to hoist arguments of val, they are guaranteed to be loop invariants
	// but not necessarily hoistable
	for _, arg := range val.Args {
		if arg.Type.IsMemory() {
			// TODO: RETHINK ABOUT THIS
			if !isMemoryDef(arg) {
				continue
			}
		}
		if _, e1 := li.invariants[arg]; e1 {
			hoisted, e2 := h.hoisted[arg]
			if !e2 {
				if !h.tryHoist(loop, li, arg) {
					return false
				}
			} else if !hoisted {
				return false
			}
		} else {
			assert(arg.Type.IsMemory() || h.sdom.IsAncestorEq(arg.Block, loop.header),
				"must define outside loop")
		}
	}

	h.hoisted[val] = false

	if !loop.IsRotatedForm() {
		return false
	}

	// Hoist the entire bound check to loop land after rotation
	if isHoistableBoundCheck(val) {
		h.hoistBoundCheck(loop, val)
		fmt.Printf("Hoist bound check %v\n", val)
		return true
	}

	// This catches most common case, e.g. arithmetic, bit operation, etc.
	if isSpeculativeValue(val) {
		assert(val.MemoryArg() == nil, "sanity check")
		h.hoist(loop.land, val)
		fmt.Printf("HoistSimple %v\n", val.LongString())
		return true
	}

	// Instructions are selected ones? The protagonist of the whole story
	if isConservativeCandidate(val) {
		// Instructions are guaranteed to execute unconditionally?
		if !alwaysExecute(h.sdom, loop, h.panicExits, val) {
			fmt.Printf("!not execute unconditional%v\n", val.LongString())
			return false
		}

		// Instructions may access same memory locations?
		if hasMemoryAlias(li.loads, li.stores, val) {
			fmt.Printf("!has mem alias%v\n", val)
			return false
		}

		h.hoist(loop.land, val)
		fmt.Printf("HoistComplex %v to %v\n", val.LongString(), loop.land)
		return true
	}

	fmt.Printf("!not_hoistable %v\n", val.LongString())
	return false
}

func (loop *loop) findInvariant(ln *loopnest) *loopInvariants {
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

		changed := true
		first := true
		for changed {
			numInvar := len(invariants)
			for _, value := range block.Values {
				if first {
					if value.Op == OpLoad {
						loads = append(loads, value)
					} else if value.Op == OpStore {
						stores = append(stores, value)
					} else if value.Op.IsCall() {
						// bail out the compilation if too complicated, for example, loop
						// involves Calls. Theoretically we can hoist Call as long as it
						// does not impose any observable side effects, e.g. only reads
						// memory or dont access memory at all, but unfortunate we may run
						// alias analysis in advance to get such facts, that some what
						// heavy for this pass at present, so we give up further motion
						// once loop blocks involve Calls
						// TODO: For intrinsic functions, we know their behaviors they
						// can be special processed in the future.
						return nil
					}
				}

				isInvariant := true
				for _, use := range value.Args {
					if use.Type.IsMemory() {
						// Discard last memory value
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
			changed = (len(invariants) != numInvar)
			first = false
		}
	}
	return &loopInvariants{
		invariants: invariants,
		loads:      loads,
		stores:     stores,
	}
}

func (h *hoister) fixMemoryState(loop *loop, startMem, endMem []*Value) {
	entry := loop.guard.Preds[0].b
	lastMem := endMem[entry.ID]

	oldLastMem := lastMem
	for _, val := range loop.land.Values {
		if arg := val.MemoryArg(); arg != nil {
			val.SetArg(len(val.Args)-1, lastMem)
		}
		if isMemoryDef(val) {
			lastMem = val
		}
	}
	// If loop land blocks contains memory def, memory state of loop header
	// should be updated as well.
	if oldLastMem != lastMem {
		loopStartMem := startMem[loop.header.ID]
		if loopStartMem == nil {
			panic("Why")
		} else if loopStartMem.Op == OpPhi {
			for idx, pred := range loop.header.Preds {
				if pred.b == loop.latch {
					loopStartMem.SetArg(1-idx, lastMem)
					break
				}
			}
		} else {
			loop.header.replaceUses(loopStartMem, lastMem)
		}
	}

	// This only replaces old memory state with new state, unordered map should okay
	for exit := range h.panicExits {
		panicVal := exit.Values[0]
		assert(panicVal.Op == OpPanicBounds || panicVal.Op == OpPanicExtend,
			"must be panic call")
		panicVal.SetArg(len(panicVal.Args)-1, lastMem)
	}
}

func looprotatetest(f *Func) {
	if f.Name != "rewriteValuegeneric_OpNeqPtr" {
		return
	}

	loopnest := f.loopnest()
	if loopnest.hasIrreducible || len(loopnest.loops) == 0 {
		return
	}

	for _, loop := range loopnest.loops {
		f.RotateLoop(loop)
	}
}

// licm stands for Loop Invariant Code Motion, it hoists expressions that computes
// the same value outside loop
func licm(f *Func) {
	// if f.Name != "(*Encoding).Encode" {
	// 	return
	// }
	// if f.Name != "(*regAllocState).placeSpills" {
	// 	return
	// }

	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}

	h := &hoister{
		fn:         f,
		panicExits: make(map[*Block]bool),
		hoisted:    make(map[*Value]bool),
	}
	startMem, endMem := computeMemState(f)
	loopnest.assembleChildren()
	loopnest.findExits()
	lcssa := make(map[*loop]bool, 0)

	// sort.SliceStable(loopnest.loops, func(i, j int) bool {
	// 	return loopnest.loops[i].header.ID < loopnest.loops[j].header.ID
	// })

	for _, loop := range loopnest.loops {
		lcssa[loop] = f.BuildLoopCloseForm(loopnest, loop)
	}
	for _, loop := range loopnest.loops {
		if yes := lcssa[loop]; !yes {
			continue
		}
		// fmt.Printf("==Loop%v %v\n", yes, loop)
		// Rotate the loop, it creates a home for hoistable Values
		if !f.RotateLoop(loop) {
			continue
		}

		// if loop != nil {
		// 	continue
		// }

		li := loop.findInvariant(loopnest)
		if li == nil || len(li.invariants) == 0 {
			continue
		}

		if !loop.CreateLoopLand(f) {
			f.Fatalf("Can not create loop land for %v", loop.LongString())
		}
		// Run first iteration to simplifiy CFG by hoisting bound check
		// Run second iteration because first iteration may reveals extra
		// loop invariants
		keys := li.stableKeys()
		h.sdom = f.Sdom()
		for iter := 0; iter < 2; iter++ {
			fmt.Printf("== Run LICM Iter%d: %v %v %v\n", iter, keys, f.Name, loop.LongString())
			for _, val := range keys {
				h.tryHoist(loop, li, val)
			}
			if len(h.panicExits) == 0 {
				break
			}
			// Remember only hoisted Values, give the second chance for others
			hoisted := make(map[*Value]bool)
			for k, v := range h.hoisted {
				if v {
					hoisted[k] = true
				}
			}
			h.hoisted = hoisted
		}
		// At this point, the loop CFG shape is fixed, fix broken memory state
		h.fixMemoryState(loop, startMem, endMem)
		// TODO: pass.stats
	}
}
