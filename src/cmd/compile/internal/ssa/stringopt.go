// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"fmt"
)

func stringopt(fn *Func) {
	// Find all runtime.concatstring calls
	for _, b := range fn.Blocks {
		for _, v := range b.Values {
			if v.Op != OpStaticLECall {
				continue
			}

			// Get the AuxCall to check function name
			aux, ok := v.Aux.(*AuxCall)
			if !ok || aux.Fn == nil {
				continue
			}

			// Check if this is a concatstring call
			fnName := aux.Fn.String()
			if !isConcatString(fnName) {
				continue
			}

			// Try to optimize the concatenation
			optimized := optimizeConcatString(fn, b, v, aux, fnName)
			fmt.Printf("optimized: %v %v\n", optimized, fn.Name)

			if fn.pass.debug > 0 && optimized {
				// fn.Warnl(b.Pos, "Optimize concatstring %v", fnName)
				fn.Warnl(b.Pos, "Optimize concatstring %v", fnName)
			}
		}
	}
}

func isConcatString(fnName string) bool {
	return fnName == "runtime.concatstring2" ||
		fnName == "runtime.concatstring3" ||
		fnName == "runtime.concatstring4" ||
		fnName == "runtime.concatstring5" ||
		fnName == "runtime.concatstrings"
}

// optimizeConcatString attempts to optimize a string concatenation call
func optimizeConcatString(fn *Func, b *Block, call *Value, aux *AuxCall, fnName string) bool {
	// For concatstring2-5, arguments are: buf, str1, str2, ..., mem
	// We want to optimize when all string arguments are constant

	nargs := len(call.Args)
	if nargs < 3 {
		// At least buf, one string, mem are required
		return false
	}

	// Check if all string arguments can be traced back to constant strings
	stringArgs := call.Args[1 : nargs-1]
	constStrings := make([]string, 0, len(stringArgs))
	allConst := true
	for _, arg := range stringArgs {
		str, ok := extractConstString(arg)
		if !ok {
			// Not all arguments are constant strings, can't optimize
			allConst = false
			break
		}
		constStrings = append(constStrings, str)
	}

	if !allConst {
		return false
	}

	// All arguments are constant strings! Concatenate them at compile time
	result := ""
	for _, s := range constStrings {
		result += s
	}

	// Replace this runtime.concatstring call with constant string
	newConst := fn.ConstString(types.Types[types.TSTRING], result)

	for _, v := range b.Values {
		switch v.Op {
		case OpSelectN:
			if v.Type.IsMemory() && len(v.Args) > 0 && v.Args[0] == call {
				memArg := call.Args[nargs-1]
				v.copyOf(memArg)
				continue
			}
			if v.Type.IsString() && len(v.Args) > 0 && v.Args[0] == call {
				v.copyOf(newConst)
				continue
			}
		}
	}
	call.copyOf(newConst)

	return true
}

// extractConstString tries to extract a constant string value from a Value
// It traces through OpStringMake and other operations to find OpConstString
func extractConstString(v *Value) (string, bool) {
	// Handle different cases
	switch v.Op {
	case OpConstString:
		// Direct constant string - this is the ideal case
		if v.Aux != nil {
			return auxToString(v.Aux), true
		}
		return "", true

	case OpStringMake:
		return "", false

	case OpLoad:
		// String loaded from memory - might be a local variable
		return "", false

	default:
		// Try to trace through single-argument operations that might be wrappers
		if len(v.Args) == 1 && v.Type != nil && v.Type.IsString() {
			return extractConstString(v.Args[0])
		}
		return "", false
	}
}
