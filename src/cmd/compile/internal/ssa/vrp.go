// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "fmt"

// ----------------------------------------------------------------------------
// Value Range Propagation
//
// Described in Jason R. C. Patterson: Accurate Static Branch Prediction by Value
// Range Propagation. PLDI 1995

// Three level lattice holds compile time knowledge about SSA value
const (
	top    int8 = iota // undefined
	vrange             // value range
	bottom             // not a constant
)

type lattice struct {
	tag   int8   // lattice type
	lower *Value // constant value
	upper *Value
}

func (lt lattice) isConst() bool {
	if lt.tag != vrange {
		return false
	}
	if lt.lower == nil || lt.upper == nil {
		return false
	}
	if lt.lower == lt.upper {
		return true
	}
	return false
}

type worklist struct {
	f            *Func               // the target function to be optimized out
	edges        []Edge              // propagate constant facts through edges
	uses         []*Value            // re-visiting set
	visited      map[Edge]bool       // visited edges
	latticeCells map[*Value]lattice  // constant lattices
	defUse       map[*Value][]*Value // def-use chains for some values
	defBlock     map[*Value][]*Block // use blocks of def
	visitedBlock []bool              // visited block
}

func vrp(f *Func) {
	if f.Name != "f1" {
		return
	}

	var t worklist
	t.f = f
	t.edges = make([]Edge, 0)
	t.visited = make(map[Edge]bool)
	t.edges = append(t.edges, Edge{f.Entry, 0})
	t.defUse = make(map[*Value][]*Value)
	t.defBlock = make(map[*Value][]*Block)
	t.latticeCells = make(map[*Value]lattice)
	t.visitedBlock = f.Cache.allocBoolSlice(f.NumBlocks())
	defer f.Cache.freeBoolSlice(t.visitedBlock)

	// build it early since we rely heavily on the def-use chain later
	t.buildDefUses()

	// pick up either an edge or SSA value from worklilst, process it
	for {
		if len(t.edges) > 0 {
			edge := t.edges[0]
			t.edges = t.edges[1:]
			if _, exist := t.visited[edge]; !exist {
				dest := edge.b
				destVisited := t.visitedBlock[dest.ID]

				// mark edge as visited
				t.visited[edge] = true
				t.visitedBlock[dest.ID] = true
				for _, val := range dest.Values {
					if val.Op == OpPhi || !destVisited {
						t.visitValue(val)
					}
				}
				// propagates constants facts through CFG, taking condition test
				// into account
				if !destVisited {
					t.propagate(dest)
				}
			}
			continue
		}
		if len(t.uses) > 0 {
			use := t.uses[0]
			t.uses = t.uses[1:]
			t.visitValue(use)
			continue
		}
		break
	}
	for v, lt := range t.latticeCells {
		fmt.Printf("==VRP%v {%v,%v,%v}\n", v, lt.tag, lt.lower, lt.upper)
	}
}

func equals(a, b lattice) bool {
	if a == b {
		// fast path
		return true
	}
	if a.tag != b.tag {
		return false
	}
	if a.tag == vrange {
		// The same content of const value may be different, we should
		// compare with auxInt instead
		return true
	}
	return true
}

func (t *worklist) getLatticeCell(val *Value) lattice {
	lt, exist := t.latticeCells[val]
	if !exist {
		return lattice{top, nil, nil} // optimistically for un-visited value
	}
	return lt
}

func isConst(val *Value) bool {
	switch val.Op {
	case OpConst64, OpConst32, OpConst16, OpConst8,
		OpConstBool, OpConst32F, OpConst64F:
		return true
	default:
		return false
	}
}

// buildDefUses builds def-use chain for some values early, because once the
// lattice of a value is changed, we need to update lattices of use. But we don't
// need all uses of it, only uses that can become constants would be added into
// re-visit worklist since no matter how many times they are revisited, uses which
// can't become constants lattice remains unchanged, i.e. Bottom.
func (t *worklist) buildDefUses() {
	for _, block := range t.f.Blocks {
		for _, val := range block.Values {
			for _, arg := range val.Args {
				// find its uses, only uses that can become constants take into account
				if _, exist := t.defUse[arg]; !exist {
					t.defUse[arg] = make([]*Value, 0, arg.Uses)
				}
				t.defUse[arg] = append(t.defUse[arg], val)
			}
		}
		for _, ctl := range block.ControlValues() {
			// for control values that can become constants, find their use blocks
			t.defBlock[ctl] = append(t.defBlock[ctl], block)
		}
	}
}

// addUses finds all uses of value and appends them into work list for further process
func (t *worklist) addUses(val *Value) {
	for _, use := range t.defUse[val] {
		if val == use {
			// Phi may refer to itself as uses, ignore them to avoid re-visiting phi
			// for performance reason
			continue
		}
		t.uses = append(t.uses, use)
	}
	for _, block := range t.defBlock[val] {
		if t.visitedBlock[block.ID] {
			t.propagate(block)
		}
	}
}

func computeLattice(f *Func, val *Value, args ...*Value) *Value {
	constValue := f.newValue(val.Op, val.Type, f.Entry, val.Pos)
	constValue.AddArgs(args...)
	matched := rewriteValuegeneric(constValue)
	if matched {
		if isConst(constValue) {
			return constValue
		}
	}
	constValue.reset(OpInvalid)
	return nil
}

func (t *worklist) visitValue(val *Value) {
	oldLt := t.getLatticeCell(val)
	defer func() {
		// re-visit all uses of value if its lattice is changed
		newLt := t.getLatticeCell(val)
		if !equals(newLt, oldLt) {
			if int8(oldLt.tag) > int8(newLt.tag) {
				t.f.Fatalf("Must lower lattice\n")
			}
			t.addUses(val)
		}
	}()

	switch val.Op {
	// they are constant values, aren't they?
	case OpConst64, OpConst32, OpConst16, OpConst8,
		OpConstBool, OpConst32F, OpConst64F:
		t.latticeCells[val] = lattice{vrange, val, val}
	// lattice value of copy(x) actually means lattice value of (x)
	case OpCopy:
		t.latticeCells[val] = t.getLatticeCell(val.Args[0])
	case
		// add
		OpAdd64, OpAdd32, OpAdd16, OpAdd8,
		OpAdd32F, OpAdd64F:
		lt1 := t.getLatticeCell(val.Args[0])
		lt2 := t.getLatticeCell(val.Args[1])

		if lt1.tag == vrange && lt2.tag == vrange {
			lower := computeLattice(t.f, val, lt1.lower, lt2.lower)
			upper := computeLattice(t.f, val, lt1.upper, lt2.upper)
			t.latticeCells[val] = lattice{vrange, lower, upper}
		} else {
			if lt1.tag == bottom || lt2.tag == bottom {
				t.latticeCells[val] = lattice{bottom, nil, nil}
			} else {
				t.latticeCells[val] = lattice{top, nil, nil}
			}
		}
	case OpLess64, OpLess32, OpLess16, OpLess8,
		OpLess64U, OpLess32U, OpLess16U, OpLess8U,
		OpLess32F, OpLess64F:
		lt1 := t.getLatticeCell(val.Args[0])
		lt2 := t.getLatticeCell(val.Args[1])
		if lt1.tag == vrange && lt2.tag == vrange {
			lower := computeLattice(t.f, val, lt1.lower, lt2.lower)
			upper := computeLattice(t.f, val, lt1.upper, lt2.upper)
			t.latticeCells[val] = lattice{vrange, lower, upper}
		} else if lt1.tag == vrange {
			t.latticeCells[val] = lattice{vrange, lt1.upper, nil}
		} else if lt2.tag == vrange {
			t.latticeCells[val] = lattice{vrange, nil, lt2.lower}
		} else {
			if lt1.tag == bottom || lt2.tag == bottom {
				t.latticeCells[val] = lattice{bottom, nil, nil}
			} else {
				t.latticeCells[val] = lattice{top, nil, nil}
			}
		}
	default:
		// Any other type of value cannot be a constant, they are always worst(Bottom)
	}
}

// propagate propagates constants facts through CFG. If the block has single successor,
// add the successor anyway. If the block has multiple successors, only add the
// branch destination corresponding to lattice value of condition value.
func (t *worklist) propagate(block *Block) {
	switch block.Kind {
	case BlockExit, BlockRet, BlockRetJmp, BlockInvalid:
		// control flow ends, do nothing then
		break
	case BlockDefer:
		// we know nothing about control flow, add all branch destinations
		t.edges = append(t.edges, block.Succs...)
	case BlockFirst:
		fallthrough // always takes the first branch
	case BlockPlain, BlockIf:
		t.edges = append(t.edges, block.Succs[0])
	default:
		t.f.Fatalf("All kind of block should be processed above.")
	}
}
