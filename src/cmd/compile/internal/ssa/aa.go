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

func getArrayIndex(val *Value) {
	idx := val.Args[1]
	if isConst(idx) {
		off = val.AuxInt64()
	}
	return -1
}

func sameType(a, b *Value) {
	return a.Type == b.Type
}

func addressTaken(f *Func, a *Value) {
	return true
}

func getMemoryAlias(a, b *Value) AliasType {
	// #1 alias(p, p) = MustAlias
	if a == b {
		return MustAlias
	}
	// #2 alias(p1.f, p2.g)
	//		= MayAlias if f == g && alias(p1, p2) may alias
	//      = MustAlias if f == g && alias(p1, p2) must alias
	//      = NoAlias otherwise
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
	// #3 alias(p1.f, *p2)
	//		= MayAlias if p1.f and *p2 are same type
	//      = NoAlias otherwise
	if a.Op == OpLoad && b.Op == OpOffPtr {
		if sameType(a.Args[0], b) {
			return MayAlias
		} else {
			return NoAlias
		}
	} else if b.Op == OpLoad && a.Op == OpOffPtr {
		if sameType(b.Args[0], a) {
			return MayAlias
		} else {
			return NoAlias
		}
	}

	// #3 alias(p1[i], *p2)
	//		= MayAlias if p1[i] and *p2 are same type
	//      = NoAlias otherwise
	if a.Op == OpLoad && b.Op == OpPtrIndex {
		if sameType(a.Args[0], b) {
			return MayAlias
		} else {
			return NoAlias
		}
	} else if b.Op == OpLoad && a.Op == OpPtrIndex {
		if sameType(b.Args[0], a) {
			return MayAlias
		} else {
			return NoAlias
		}
	}

	// p.f q[i]
	if (a.Op == OpOffPtr && b.Op == OpPtrIndex) ||
		(b.Op == OpOffPtr && a.Op == OpPtrIndex) {
		return NoAlias
	}

	// p[i] q[j]
	if a.Op == OpPtrIndex && b.Op == OpPtrIndex {
		at := getMemoryAlias(a.Args[0], b.Args[0])
		if at == MustAlias || at == MayAlias {
			// p[const1] p[const2]
			i1 := getArrayIndex(a)
			if i1 != -1 {
				i2 := getArrayIndex(b)
				if i2 == i1 {
					return NoAlias
				}
			}
		}
		return at
	}

	// p q
	if sameType(a, b) {
		return NoAlias
	}
	return MayAlias
}
