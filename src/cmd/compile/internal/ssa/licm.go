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
	fn      *Func
	sdom    SparseTree
	hoisted map[*Value]bool
}

func (li loopInvariants) stableKeys() []*Value {
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
		OpPanicBounds, OpPanicExtend,
		OpPubBarrier,
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
			// fmt.Printf("#%v#%v#%v\n", loadPtr.LongString(), storePtr.LongString(), at)
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
func alwaysExecute(sdom SparseTree, loop *loop, val *Value) bool {
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

func isConservativeCandidate(val *Value) bool {
	// The protagonist of the whole story
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
	// TODO: Store produces memory, all uses should be updated
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
// all     7142, store34, load3011, nilcheck 914, boundcheckNan  loop exit belongs to current loop
// all     7186, store34, load3023, nilcheck 918, boundcheckNan lcssa allow mutiple exit
// all     simple 55260, complex 4538
// all     simple 57369, complex 5233
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
			assert(arg.Op == OpUnknown || arg.Op == OpInvalid ||
				arg.Type.IsMemory() || h.sdom.IsAncestorEq(arg.Block, loop.header),
				"arg %v must define outside loop", arg)
		}
	}

	h.hoisted[val] = false
	isHoistableBoundCheck(val)

	if !loop.IsRotatedForm() {
		return false
	}

	// This catches most common case, e.g. arithmetic, bit operation, etc.
	if !isAccessMemory(val) {
		assert(val.MemoryArg() == nil, "sanity check")
		h.hoist(loop.land, val)
		fmt.Printf("HoistSimple %v\n", val.LongString())
		return true
	}

	// Instructions are selected ones?
	if isConservativeCandidate(val) {
		// Instructions are guaranteed to execute unconditionally?
		if !alwaysExecute(h.sdom, loop, val) {
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
		for _, value := range block.Values {
			if value.Op == OpLoad {
				loads = append(loads, value)
			} else if value.Op == OpStore {
				stores = append(stores, value)
			} else if value.Op.IsCall() {
				sym := auxToCall(value.Aux)
				if isSameCall(sym, "runtime.memequal") ||
					isSameCall(sym, "runtime.ifaceeq") ||
					isSameCall(sym, "runtime.efaceeq") ||
					isSameCall(sym, "runtime.dumpint") ||
					isSameCall(sym, "runtime.printlock") {
					continue
				}
				// Simple statistics show that 60% of LICM candidate loops contain
				// at least one function call, in the absence of inter-procedural
				// modref analysis we will exclude some intrinsic functions as
				// much as possible because we know exactly how they behave, for
				// the rest of the function calls , we are not sure if they affect
				// the correctness of the tbaa so we conservatively abstain from
				// continuing the optimisation
				return nil
			}
		}
		// If basic block is located in a nested loop rather than directly in the
		// current loop, it will not be processed.
		if ln.b2l[block.ID] != loop {
			continue
		}

		changed := true
		for changed {
			numInvar := len(invariants)
			for _, value := range block.Values {
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
		}
	}
	// fmt.Printf("==%v %v %v %v", loop.LongString(), invariants, loads, stores)

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
}

// licm stands for Loop Invariant Code Motion, it hoists expressions that computes
// the same value outside loop
func licm(f *Func) {
	// if f.Name != "critical" && f.Name != "tracebackHexdump" {
	// 	return
	// }
	// if f.Name != "(*regAllocState).placeSpills??" {
	// 	return
	// }
	// if f.Name != "(*Reader).Peek" {
	// 	return
	// }
	// if f.Name != "(*Frames).Next" {
	// 	return
	// }
	if f.Name != "getempty" {
		return
	}

	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}

	h := &hoister{
		fn:      f,
		hoisted: make(map[*Value]bool),
	}
	loopnest.assembleChildren()
	loopnest.findExits()
	lcssa := make(map[*loop]bool, 0)

	// sort.SliceStable(loopnest.loops, func(i, j int) bool {
	// 	return loopnest.loops[i].header.ID < loopnest.loops[j].header.ID
	// })

	for _, loop := range loopnest.loops {
		lcssa[loop] = f.BuildLoopClosedForm(loopnest, loop)
	}
	startMem, endMem := computeMemState(f)
	for _, loop := range loopnest.loops {
		if yes := lcssa[loop]; !yes {
			fmt.Printf("==NOLCSSA\n")
			continue
		} else {
			fmt.Printf("==YESLCSSA\n")
		}
		// fmt.Printf("==Loop%v %v\n", yes, loop)
		// Rotate the loop, it creates a home for hoistable Values
		if !f.RotateLoop(loop) {
			continue
		}

		if loop != nil {
			break
			// continue
		}

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
		for _, val := range keys {
			h.tryHoist(loop, li, val)
		}
		// At this point, the loop CFG shape is fixed, fix broken memory state
		h.fixMemoryState(loop, startMem, endMem)
		// TODO: pass.stats
	}
}
