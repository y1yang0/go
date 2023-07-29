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

func destructPtr(val *Value) (ptr, off) {
	ptr := nil
	off := -1
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

func getMemoryAlias(a, b *Value) {
	// #1 identical values are always alias each other
	if a == b {
		return MustAlias
	}
	// #2 different static types are always not alias
	if a.Type != b.Type {
		return NoAlias
	}
	ptr1, off1 := destructPtr(a)
	ptr2, off2 := destructPtr(b)
	if ptr != nil && ptr2 != nil {
		return MustAlias
	}
	return MayAlias
}
