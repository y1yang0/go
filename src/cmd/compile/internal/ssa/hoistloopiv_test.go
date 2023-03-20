package ssa

import (
	"cmd/compile/internal/types"
	"testing"
)

func checkValueMotion(t *testing.T, fun fun, valName, expectedBlock string) {
	for _, b := range fun.f.Blocks {
		for _, v := range b.Values {
			if v == fun.values[valName] {
				if fun.blocks[expectedBlock] != b {
					t.Errorf("Error: %v\n", v.LongString())
				}
			}
		}
	}
}

//	var d int
//
//	for i := 0; i < 10; i++ {
//		t := 1 + 10
//		d = i + t
//	}
//
// t should be hoisted to dominator block of loop header
func TestHoistLoopIVSimple1(t *testing.T) {
	c := testConfig(t)
	fun := c.Fun("b1",
		Bloc("b1",
			Valu("mem", OpInitMem, types.TypeMem, 0, nil),
			Valu("zero", OpConst64, c.config.Types.Int64, 0, nil),
			Valu("one", OpConst64, c.config.Types.Int64, 1, nil),
			Valu("ten", OpConst64, c.config.Types.Int64, 10, nil),
			Goto("b2")),
		Bloc("b2",
			Valu("i", OpPhi, c.config.Types.Int64, 0, nil, "one", "i2"),
			Valu("d", OpPhi, c.config.Types.Int64, 0, nil, "zero", "d2"),
			Valu("cmp", OpLess64, c.config.Types.Bool, 0, nil, "i", "ten"),
			If("cmp", "b3", "b4")),
		Bloc("b3",
			Valu("loopiv", OpAdd64, c.config.Types.Int64, 0, nil, "one", "ten"),
			Valu("d2", OpAdd64, c.config.Types.Int64, 0, nil, "loopiv", "d"),
			Valu("i2", OpAdd64, c.config.Types.Int64, 0, nil, "i", "one"),
			Goto("b2")),
		Bloc("b4",
			Exit("mem")))

	CheckFunc(fun.f)
	hoistLoopInvariant(fun.f)
	CheckFunc(fun.f)
	checkValueMotion(t, fun, "loopiv", "b1")
}

//	var d int
//	var p = 15
//
//	for i := 0; i < 10; i++ {
//		t := 1 % p
//		d = i + t
//	}
//
// t should be hoisted to dominator block of loop header
func TestHoistLoopIVSimple2(t *testing.T) {
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
			Valu("loopiv", OpMod64, c.config.Types.Int64, 0, nil, "one", "p"),
			Valu("d2", OpAdd64, c.config.Types.Int64, 0, nil, "loopiv", "d"),
			Valu("i2", OpAdd64, c.config.Types.Int64, 0, nil, "i", "one"),
			Goto("b2")),
		Bloc("b4",
			Exit("mem")))

	CheckFunc(fun.f)
	hoistLoopInvariant(fun.f)
	CheckFunc(fun.f)
	checkValueMotion(t, fun, "loopiv", "b1")
}
