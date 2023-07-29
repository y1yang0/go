// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// Type Based Alias Analysis

type AliasType uint

const (
	MustAlias AliasType = iota
	MayAlias
	NoAlias
)

func isConst(v *Value) bool {
	switch v.Op {
	case OpConst64, OpConst32, OpConst16, OpConst8:
		return true
	}
	return false
}

func destructPtr(val *Value) (*Value, int64) {
	var ptr *Value
	var off int64
	switch val.Op {
	case OpOffPtr:
		ptr = val.Args[0]
		off = val.AuxInt64()
	case OpPtrIndex:
		ptr = val.Args[0]
		idx := val.Args[1]
		if isConst(idx) {
			off = val.AuxInt64()
		}
	}
	return ptr, off
}

func getMemoryAlias(a, b *Value) AliasType {
	if a == b {
		return MustAlias
	}
	if a.Op == OpOffPtr && b.Op == OpOffPtr {
		ptr1 := a.Args[0]
		ptr2 := b.Args[0]
		off1 := a.AuxInt64()
		off2 := b.AuxInt64()
		if off1 == off2 {
			at := getMemoryAlias(ptr1, ptr2)
			if at == MayAlias {
				return MayAlias
			} else if at == MustAlias {
				return MustAlias
			}
		} else {
			return NoAlias
		}
	}
	// #xx deference and array index/field access may alias
	// #xx array[index] is not alias with object.field
	if (a.Op == OpOffPtr && b.Op == OpPtrIndex) ||
		(b.Op == OpOffPtr && a.Op == OpPtrIndex) {
		return NoAlias
	}
	// #2 different static types are always not alias
	if a.Type != b.Type {
		return NoAlias
	}
	return MayAlias
}
