// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"fmt"
	"sort"
	"testing"
)

// var d int
// var p = 15
//
//	for i := 0; i < 10; i++ {
//		t := 1 * p
//		d = i + t
//	}
func TestLoopRotate(t *testing.T) {
	c := testConfig(t)
	fun := c.Fun("b1",
		Bloc("b1",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("ten", OpConst64, c.config.Types.Int64, 10, nil),
			Valu("p", OpConst64, c.config.Types.Int64, 15, nil),
			Goto("b2")),
		Bloc("b2",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "one", "i2"),
			Valu("d", OpPhi, c.config.Types.Int64, 0, nil, "zero", "d2"),
			Valu("cmp", OpLess64, c.config.Types.Bool, 0, nil, "i", "ten"),
			If("cmp", "b3", "b4")),
		Bloc("b3",
			Valu("loopiv", OpMul64, c.config.Types.Int64, 0, nil, "one", "p"),
			Valu("d2", OpAdd64, c.config.Types.Int64, 0, nil, "loopiv", "d"),
			Valu("i2", OpAdd64, c.config.Types.Int64, 0, nil, "i", "one"),
			Goto("b2")),
		Bloc("b4",
			Exit("mem")))

	DoLoopRotate(fun)

	fmt.Printf("%s", fun.f)
	m := map[ID][]ID{
		1: {5},    // entry -> guard
		5: {2, 4}, // guard -> header exit
		2: {3},    // header -> body
		3: {2, 4}, // body -> header | exit
	}

	CheckBBConnection(fun, m, t)
}

//		var d int
//		var p = 15
//	    var limit = 7
//		if 0 < limit {
//			  for i := 0; i < limit; i++ {
//				  t := 1 * p
//				  d = i + t
//			  }
//		}
func TestSkipLoopAlreadyRotate(t *testing.T) {
	c := testConfig(t)
	arg1Aux := &tstAux{"arg1-aux"}

	fun := c.Fun("b1",
		Bloc("b1",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("limit", OpArg, c.config.Types.Int64, 0, arg1Aux),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("p", OpConst64, c.config.Types.Int64, 15, nil),
			Goto("b2"),
		),
		Bloc("b2",
			Valu("cmp1", OpLess64, c.config.Types.Bool, 0, nil, "zero", "limit"),
			If("cmp1", "b3", "b6")),
		Bloc("b3",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "one", "i2"),
			Valu("d", OpPhi, c.config.Types.Int64, 0, nil, "zero", "d2"),
			Goto("b4")),
		Bloc("b4",
			Valu("loopiv", OpMul64, c.config.Types.Int64, 0, nil, "one", "p"),
			Valu("d2", OpAdd64, c.config.Types.Int64, 0, nil, "loopiv", "d"),
			Goto("b5")),
		Bloc("b5",
			Valu("i2", OpAdd64, c.config.Types.Int64, 0, nil, "i", "one"),
			Valu("cmp2", OpLess64, c.config.Types.Bool, 0, nil, "i", "limit"),
			If("cmp2", "b3", "b6")),
		Bloc("b6",
			Exit("mem")))

	CheckNotDoLoopRotate(fun, t)
}

// var d int
// var p = 15
//
//	if a < 10 {
//		  for i := 0; i < 10; i++ {
//			  t := 1 * p
//			  d = i + t
//		  }
//	}
func TestSkipLoopShouldNotRotate(t *testing.T) {
	c := testConfig(t)
	arg1Aux := &tstAux{"arg1-aux"}

	fun := c.Fun("b1",
		Bloc("b1", // entry
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("a", OpArg, c.config.Types.Int64, 0, arg1Aux),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("ten", OpConst64, c.config.Types.Int64, 10, nil),
			Valu("p", OpConst64, c.config.Types.Int64, 15, nil),
			Goto("b2"),
		),
		Bloc("b2", // guard
			Valu("cmp1", OpLess64, c.config.Types.Bool, 0, nil, "a", "ten"),
			If("cmp1", "b3", "b6")),
		Bloc("b3",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "one", "i2"),
			Valu("d", OpPhi, c.config.Types.Int64, 0, nil, "zero", "d2"),
			Goto("b4")),
		Bloc("b4", // body
			Valu("loopiv", OpMul64, c.config.Types.Int64, 0, nil, "one", "p"),
			Valu("d2", OpAdd64, c.config.Types.Int64, 0, nil, "loopiv", "d"),
			Goto("b5")),
		Bloc("b5", // latch
			Valu("i2", OpAdd64, c.config.Types.Int64, 0, nil, "i", "one"),
			Valu("cmp2", OpLess64, c.config.Types.Bool, 0, nil, "i", "ten"),
			If("cmp2", "b3", "b6")),
		Bloc("b6", // exit
			Exit("mem")))

	CheckNotDoLoopRotate(fun, t)
}

func CheckNotDoLoopRotate(fun fun, t *testing.T) {
	fmt.Printf("%s", fun.f)
	if DoLoopRotate(fun) {
		t.Fatal("Should not do loop rotate")
	}
}

func DoLoopRotate(fun fun) bool {
	CheckFunc(fun.f)
	f := fun.f
	loopnest := f.loopnest()
	for _, loop := range loopnest.loops {
		if f.RotateLoop(loop) {
			return true
		}
	}
	return false
}

func mapTo[T, U any](data []T, f func(T) U) []U {
	res := make([]U, 0, len(data))

	for _, e := range data {
		res = append(res, f(e))
	}

	return res
}

func equal(a, b []ID) bool {
	if len(a) != len(b) {
		return false
	}

	ma := make(map[ID]bool, len(a))
	for _, v := range a {
		ma[v] = true
	}

	for _, v := range b {
		if _, found := ma[v]; !found {
			return false
		}
	}

	return true
}

func CheckBBConnection(fun fun, connection map[ID][]ID, t *testing.T) {
	CheckFunc(fun.f)
	for _, bb := range fun.f.Blocks {
		//exit
		if len(bb.Succs) == 0 {
			continue
		}
		ids := connection[bb.ID]
		succs := mapTo(bb.Succs, func(e Edge) ID {
			return e.Block().ID
		})
		sort.Slice(ids, func(i, j int) bool {
			return ids[i] > ids[j]
		})
		sort.Slice(succs, func(i, j int) bool {
			return succs[i] > succs[j]
		})
		if !equal(ids, succs) {
			t.Fatal("error")
		}
	}
}
