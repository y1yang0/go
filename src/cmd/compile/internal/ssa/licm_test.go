// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"fmt"
	"testing"
)

func doLICM(fun fun) {
	CheckFunc(fun.f)
	licm(fun.f)
	CheckFunc(fun.f)
}

func checkHoist(t *testing.T, fun fun, loopInvariants ...string) {
	loopHeader := fun.blocks["loopHeader"]
	// Find loop land block
	sdom := fun.f.Sdom()
	var loopLand *Block
	for _, pred := range loopHeader.Preds {
		if sdom.isAncestor(pred.b, loopHeader) {
			loopLand = pred.b
			break
		}
	}
	if loopLand == nil {
		fmt.Printf("== After LICM: %v\n", fun.f.String())
		t.Errorf("Error: loop land block not found\n")
	}
	if len(loopLand.Preds) != 1 || len(loopLand.Succs) != 1 {
		fmt.Printf("== After LICM: %v\n", fun.f.String())
		t.Errorf("Error: bad loop land\n")
	}
	// Find expected loop invariant from loop land
	cnt := 0
	for _, li := range loopInvariants {
		for _, val := range loopLand.Values {
			if val == fun.values[li] {
				cnt++
				break
			}
		}
	}

	if cnt != len(loopInvariants) {
		fmt.Printf("== After LICM: %v\n", fun.f.String())
		t.Errorf("Error: loop invariant not found in loop land")
	}
}

// Hoist simple arithmetic loop invariant
//
//	for i := 0; i < 10; i++ {
//		li := 10 * 10
//	}
func TestHoistSimpleLI(t *testing.T) {
	c := testConfig(t)
	fun := c.Fun("loopEntry",
		Bloc("loopEntry",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("ten", OpConst64, c.config.Types.Int64, 10, nil),
			Goto("loopHeader")),
		Bloc("loopHeader",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "zero", "inc"),
			Valu("li", OpMul64, c.config.Types.Int64, 0, nil, "ten", "one"),
			Valu("cmp", OpLess64, c.config.Types.Bool, 0, nil, "i", "ten"),
			If("cmp", "loopLatch", "loopExit")),
		Bloc("loopLatch",
			Valu("inc", OpAdd64, c.config.Types.Int64, 0, nil, "one", "i"),
			Goto("loopHeader")),
		Bloc("loopExit",
			Exit("mem")))

	doLICM(fun)
	fmt.Printf("== After LICM: %v\n", fun.f.String())
	checkHoist(t, fun, "li")
}

// Hoist simple arithmetic but may trap execution
//
//	 func foo(arg1 int)
//		for i := 0; i < 10; i++ {
//			li := (10*10) / arg1 /*may be zero*/
//		}
//	 }
func TestHoistTrapDiv(t *testing.T) {
	c := testConfig(t)
	fun := c.Fun("loopEntry",
		Bloc("loopEntry",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("arg1", OpArg, c.config.Types.Int64, 0, nil),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("ten", OpConst64, c.config.Types.Int64, 10, nil),
			Goto("loopHeader")),
		Bloc("loopHeader",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "zero", "inc"),
			Valu("li", OpMul64, c.config.Types.Int64, 0, nil, "ten", "one"),
			Valu("li2", OpDiv64, c.config.Types.Int64, 0, nil, "li", "arg1"),
			Valu("cmp", OpLess64, c.config.Types.Bool, 0, nil, "i", "ten"),
			If("cmp", "loopLatch", "loopExit")),
		Bloc("loopLatch",
			Valu("inc", OpAdd64, c.config.Types.Int64, 0, nil, "one", "i"),
			Goto("loopHeader")),
		Bloc("loopExit",
			Exit("mem")))

	doLICM(fun)
	checkHoist(t, fun, "li", "li2")
}

// Hoist load and store from loop
//
//	for i := 0; i < 10; i++ {
//		*addr = 1
//		load := *addr1
//	}
func TestHoistLoadStore(t *testing.T) {
	c := testConfig(t)
	fun := c.Fun("loopEntry",
		Bloc("loopEntry",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("sb", OpSB, c.config.Types.Uintptr, 0, nil),
			Goto("loopHeader")),
		Bloc("loopHeader",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "zero", "inc"),
			Valu("addr", OpAddr, c.config.Types.Int8.PtrTo(), 0, nil, "sb"),
			Valu("addr1", OpAddr, c.config.Types.Int64.PtrTo(), 0, nil, "sb"),
			Valu("store", OpStore, types.TypeMem, 0, nil, "addr", "one", "mem"),
			Valu("load", OpLoad, c.config.Types.Int8, 0, nil, "addr1", "mem"),
			Valu("cmp", OpLess64, c.config.Types.Bool, 0, nil, "i", "load"),
			If("cmp", "loopLatch", "loopExit")),
		Bloc("loopLatch",
			Valu("inc", OpAdd64, c.config.Types.Int64, 0, nil, "load", "i"),
			Goto("loopHeader")),
		Bloc("loopExit",
			Exit("mem")))

	doLICM(fun)
	checkHoist(t, fun, "load", "store", "addr", "addr1")
}

// Hoist nil check from loop
func TestHoistNilCheck(t *testing.T) {
	c := testConfig(t)
	fun := c.Fun("loopEntry",
		Bloc("loopEntry",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("sb", OpSB, c.config.Types.Uintptr, 0, nil),
			Valu("addr", OpAddr, c.config.Types.Int8.PtrTo(), 0, nil, "sb"),
			Goto("loopHeader")),
		Bloc("loopHeader",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "zero", "inc"),
			Valu("nilcheck", OpNilCheck, types.TypeVoid, 0, nil, "addr", "mem"),
			Valu("cmp", OpLess64, c.config.Types.Bool, 0, nil, "i", "one"),
			If("cmp", "loopLatch", "loopExit")),
		Bloc("loopLatch",
			Valu("inc", OpAdd64, c.config.Types.Int64, 0, nil, "one", "i"),
			Goto("loopHeader")),
		Bloc("loopExit",
			Exit("mem")))

	doLICM(fun)
	checkHoist(t, fun, "nilcheck")
}

// func BenchmarkHoistIV1Opt(b *testing.B) {
// 	var d = 0
// 	var a = 3

// 	for i := 0; i < b.N; i++ {
// 		d = i + (a*10 - a + 3)
// 	}
// 	_ = d
// }

// func BenchmarkHoistIV1Manual(b *testing.B) {
// 	var d = 0
// 	var a = 3
// 	val := (a*10 - a + 3)
// 	for i := 0; i < b.N; i++ {
// 		d = i + val
// 	}
// 	_ = d
// }

// //go:noinline
// func hoistLoopIV2Opt(n, d int) {
// 	t := 0
// 	for i := 0; i < n*d; i++ {
// 		t += 1
// 	}
// 	_ = t
// }

// //go:noinline
// func hoistLoopIV2Manual(n, d int) {
// 	t := 0
// 	val := n * d
// 	for i := 0; i < val; i++ {
// 		t += 1
// 	}
// 	_ = t
// }

// func BenchmarkHoistIV2Opt(b *testing.B) {
// 	for i := 0; i < b.N; i++ {
// 		hoistLoopIV2Opt(i%10, i%5)
// 	}
// }

// func BenchmarkHoistIV2Manual(b *testing.B) {
// 	for i := 0; i < b.N; i++ {
// 		hoistLoopIV2Manual(i%10, i%5)
// 	}
// }
