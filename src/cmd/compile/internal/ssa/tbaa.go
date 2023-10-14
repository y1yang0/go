// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "fmt"

// AliasType Type-based Alias Analysis
//
// Described in
// Amer Diwan, Kathryn S. McKinley, J. Eliot B. Moss: Type-Based Alias Analysis.
// PLDI 1998
//
// TBAA relies on the fact that Golang is a type-safe language, i.e. different
// pointer types cannot be converted to each other in Golang. Under assumption,
// TBAA attempts to identify whether two pointers may point to same memory based
// on their type and value semantics. They can be summarized as follows rules:
//
//	#0 unsafe pointer may alias with anything even if their types are different
//	#1 a must aliases with b if a==b
//	#2 a.f aliases with b.g if f==g and an aliases with b
//	#3 a.f aliases with *b if they have same types
//	#4 a[i] aliases with *b if they have same types
//	#5 a.f never aliases with b[i]
//	#6 a[i] aliases with b[j] if a==b or
//	  #6' a[c1] never aliases with b[c2] if c1 != c2
//	#7 an aliases with b if they have same types
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

// GetMemoryAlias check if two pointers may point to the same memory location.
func GetMemoryAlias(a, b *Value) AliasType {
	// #0 unsafe pointer may alia with anything even if their types are different
	if a.Type.IsUnsafePtr() || b.Type.IsUnsafePtr() {
		return MayAlias
	}

	// #1 p must aliases with p
	if a == b {
		return MustAlias
	}

	// #2 p1.f aliases with p2.g if f==g and p1 aliases with p2
	if a.Op == b.Op && (a.Op == OpOffPtr || a.Op == OpAddr ||
		a.Op == OpLocalAddr || a.Op == OpAddPtr) {
		if isSamePtr(a, b) {
			return MustAlias
		}
		return NoAlias
	}

	// #5 p.f never aliases with q[i]
	if (a.Op == OpOffPtr && b.Op == OpPtrIndex) ||
		(b.Op == OpOffPtr && a.Op == OpPtrIndex) {
		return NoAlias
	}

	return MayAlias
}
