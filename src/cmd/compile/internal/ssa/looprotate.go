// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

func moveBlock(slice []*Block, from, to int) []*Block {
	if from < 0 || to < 0 || from >= len(slice) || to >= len(slice) {
		return slice
	}

	elem := slice[from]
	if from < to {
		copy(slice[from:], slice[from+1:to+1])
	} else {
		copy(slice[to+1:], slice[to:from])
	}

	slice[to] = elem
	return slice
}

// loopRotate converts loops with a check-loop-condition-at-beginning
// to loops with a check-loop-condition-at-end.
// This helps loops avoid extra unnecessary jumps.
//
//	 loop:
//	   CMPQ ...
//	   JGE exit
//	   ...
//	   JMP loop
//	 exit:
//
//	  JMP entry
//	loop:
//	  ...
//	entry:
//	  CMPQ ...
//	  JLT loop
func loopRotate(f *Func) {
	loopnest := f.loopnest()
	if loopnest.hasIrreducible {
		return
	}
	if len(loopnest.loops) == 0 {
		return
	}
	loopnest.findExits()
	for _, loop := range loopnest.loops {
		header := loop.header
		// If loop rotation is already applied, loop latch should be right after
		// all loop body blocks
		if header.Kind == BlockPlain && len(header.Succs) == 1 {
			continue
		}
		var latch *Block // b's in-loop predecessor
		for _, e := range header.Preds {
			if e.b.Kind != BlockPlain {
				continue
			}
			if loopnest.b2l[e.b.ID] != loop {
				continue
			}
			latch = e.b
		}
		if latch == nil || latch == header {
			continue
		}
		iheader, ilatch := 0, 0
		for ib, b := range f.Blocks {
			if b == header {
				iheader = ib
			} else if b == latch {
				ilatch = ib
			}
		}
		// Reordering the loop blocks from [header,body,latch] to [latch,body,header]
		f.Blocks = moveBlock(f.Blocks, iheader, ilatch)
	}
}
