// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "fmt"

// ----------------------------------------------------------------------------
// Type-based Alias Anallysis
//
// Described in
// Amer Diwan, Kathryn S. McKinley, J. Eliot B. Moss: Type-Based Alias Analysis.
// PLDI 1998
//
// TBAA relies on the fact that Golang is a type-safe language, i.e. different
// pointer types cannot be converted to each other in Golang. Under this assumption,
// TBAA attempts to identify whether two pointers may point to same memory based
// on their type and value semantics. They can be summarized as follows rules:
//
//  #1 p must aliases with p
//  #2 p1.f aliases with p2.g if f==g and p1 aliases with p2
//  #3 p1.f aliases with *p2 if they have same types
//  #4 p1[i] aliases with *p2 if they have same types
//  #5 p1.f never aliases with q[i]
//  #6 p1[i] aliases with q[j] if p==q or
//    #6' p[c1] never aliases with p[c2] if c1 != c2
//  #7 p aliases with q if they have same types
//
// I conservatively assume that any unsafe calls may break this assumption, so
// it is the responsibility of the caller to ensure this.

type AliasType uint

const (
	MustAlias AliasType = iota
	MayAlias
	NoAlias
)

func (at AliasType) String() string {
	switch at {
	case MustAlias:
		return fmt.Sprintf("MustAlias")
	case MayAlias:
		return fmt.Sprintf("MayAlias")
	case NoAlias:
		return fmt.Sprintf("NoAlias")
	}
	return fmt.Sprintf("Unknown")
}

func getArrayIndex(val *Value) int64 {
	idx := val.Args[1]
	switch idx.Op {
	case OpConst64, OpConst32, OpConst16, OpConst8:
		return idx.AuxInt64()
	}
	return -1
}

func sameType(a, b *Value) bool {
	return a.Type == b.Type
}

func addressTaken(f *Func, a *Value) bool {
	return true
}

// getMemoryAlias check if two pointers may point to the same memory location.
func GetMemoryAlias(a, b *Value) AliasType {
	// #1 p must aliases with p
	if a == b {
		return MustAlias
	}
	// #2 p1.f aliases with p2.g if f==g and p1 aliases with p2
	if a.Op == OpOffPtr && b.Op == OpOffPtr {
		off1 := a.AuxInt64()
		off2 := b.AuxInt64()
		if off1 == off2 {
			ptr1 := a.Args[0]
			ptr2 := b.Args[0]
			return GetMemoryAlias(ptr1, ptr2)
		} else {
			return NoAlias
		}
	}
	// #3 p1.f aliases with *p2 if they have same types
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

	// #4 p1[i] aliases with *p2 if they have same types
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

	// #5 p.f never aliases with q[i]
	if (a.Op == OpOffPtr && b.Op == OpPtrIndex) ||
		(b.Op == OpOffPtr && a.Op == OpPtrIndex) {
		return NoAlias
	}

	// #6 p[i] aliases with q[j] if p==q or
	if a.Op == OpPtrIndex && b.Op == OpPtrIndex {
		at := GetMemoryAlias(a.Args[0], b.Args[0])
		if at == MustAlias || at == MayAlias {
			// #6' p[c1] never aliases with p[c2] if c1 != c2
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

	// #7 p aliases with q if they have same types
	if !sameType(a, b) {
		return NoAlias
	}

	return MayAlias
}
