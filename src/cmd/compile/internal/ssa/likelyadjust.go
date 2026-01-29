// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"fmt"
)

type loop struct {
	header *Block // The header node of this (reducible) loop
	outer  *loop  // loop containing this loop

	// Next three fields used by regalloc and/or
	// aid in computation of inner-ness and list of blocks.
	nBlocks int32 // Number of blocks in this loop but not within inner loops
	depth   int16 // Nesting depth of the loop; 1 is outermost.
	isInner bool  // True if never discovered to contain a loop

	// True if all paths through the loop have a call.
	// Computed and used by regalloc; stored here for convenience.
	containsUnavoidableCall bool
}

// outerinner records that outer contains inner
func (sdom SparseTree) outerinner(outer, inner *loop) {
	// There could be other outer loops found in some random order,
	// locate the new outer loop appropriately among them.

	// Outer loop headers dominate inner loop headers.
	// Use this to put the "new" "outer" loop in the right place.
	oldouter := inner.outer
	for oldouter != nil && sdom.isAncestor(outer.header, oldouter.header) {
		inner = oldouter
		oldouter = inner.outer
	}
	if outer == oldouter {
		return
	}
	if oldouter != nil {
		sdom.outerinner(oldouter, outer)
	}

	inner.outer = outer
	outer.isInner = false
}

type loopnest struct {
	f              *Func
	b2l            []*loop
	po             []*Block
	sdom           SparseTree
	loops          []*loop
	hasIrreducible bool // TODO current treatment of irreducible loops is very flaky, if accurate loops are needed, must punt at function level.
}

const (
	blDEFAULT = 0
	blMin     = blDEFAULT
	blCALL    = 1
	blRET     = 2
	blEXIT    = 3
)

var bllikelies = [4]string{"default", "call", "ret", "exit"}

func describePredictionAgrees(b *Block, prediction BranchPrediction) string {
	s := ""
	if prediction == b.Likely {
		s = " (agrees with previous)"
	} else if b.Likely != BranchUnknown {
		s = " (disagrees with previous, ignored)"
	}
	return s
}

func describeBranchPrediction(f *Func, b *Block, likely, not int8, prediction BranchPrediction) {
	f.Warnl(b.Pos, "Branch prediction rule %s < %s%s",
		bllikelies[likely-blMin], bllikelies[not-blMin], describePredictionAgrees(b, prediction))
}

func likelyadjust(f *Func) {
	// The values assigned to certain and local only matter
	// in their rank order.  0 is default, more positive
	// is less likely. It's possible to assign a negative
	// unlikeliness (though not currently the case).
	certain := f.Cache.allocInt8Slice(f.NumBlocks()) // In the long run, all outcomes are at least this bad. Mainly for Exit
	defer f.Cache.freeInt8Slice(certain)
	local := f.Cache.allocInt8Slice(f.NumBlocks()) // for our immediate predecessors.
	defer f.Cache.freeInt8Slice(local)

	po := f.postorder()
	nest := f.loopnest()
	b2l := nest.b2l

	for _, b := range po {
		switch b.Kind {
		case BlockExit:
			// Very unlikely.
			local[b.ID] = blEXIT
			certain[b.ID] = blEXIT

			// Ret, it depends.
		case BlockRet, BlockRetJmp:
			local[b.ID] = blRET
			certain[b.ID] = blRET

			// Calls. TODO not all calls are equal, names give useful clues.
			// Any name-based heuristics are only relative to other calls,
			// and less influential than inferences from loop structure.
		case BlockDefer:
			local[b.ID] = blCALL
			certain[b.ID] = max(blCALL, certain[b.Succs[0].b.ID])

		default:
			if len(b.Succs) == 1 {
				certain[b.ID] = certain[b.Succs[0].b.ID]
			} else if len(b.Succs) == 2 {
				// If successor is an unvisited backedge, it's in loop and we don't care.
				// Its default unlikely is also zero which is consistent with favoring loop edges.
				// Notice that this can act like a "reset" on unlikeliness at loops; the
				// default "everything returns" unlikeliness is erased by min with the
				// backedge likeliness; however a loop with calls on every path will be
				// tagged with call cost. Net effect is that loop entry is favored.
				b0 := b.Succs[0].b.ID
				b1 := b.Succs[1].b.ID
				certain[b.ID] = min(certain[b0], certain[b1])

				l := b2l[b.ID]
				l0 := b2l[b0]
				l1 := b2l[b1]

				prediction := b.Likely
				// Weak loop heuristic -- both source and at least one dest are in loops,
				// and there is a difference in the destinations.
				// TODO what is best arrangement for nested loops?
				if l != nil && l0 != l1 {
					noprediction := false
					switch {
					// prefer not to exit loops
					case l1 == nil:
						prediction = BranchLikely
					case l0 == nil:
						prediction = BranchUnlikely

						// prefer to stay in loop, not exit to outer.
					case l == l0:
						prediction = BranchLikely
					case l == l1:
						prediction = BranchUnlikely
					default:
						noprediction = true
					}
					if f.pass.debug > 0 && !noprediction {
						f.Warnl(b.Pos, "Branch prediction rule stay in loop%s",
							describePredictionAgrees(b, prediction))
					}

				} else {
					// Lacking loop structure, fall back on heuristics.
					if certain[b1] > certain[b0] {
						prediction = BranchLikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, certain[b0], certain[b1], prediction)
						}
					} else if certain[b0] > certain[b1] {
						prediction = BranchUnlikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, certain[b1], certain[b0], prediction)
						}
					} else if local[b1] > local[b0] {
						prediction = BranchLikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, local[b0], local[b1], prediction)
						}
					} else if local[b0] > local[b1] {
						prediction = BranchUnlikely
						if f.pass.debug > 0 {
							describeBranchPrediction(f, b, local[b1], local[b0], prediction)
						}
					}
				}
				if b.Likely != prediction {
					if b.Likely == BranchUnknown {
						b.Likely = prediction
					}
				}
			}
			// Look for calls in the block.  If there is one, make this block unlikely.
			for _, v := range b.Values {
				if opcodeTable[v.Op].call {
					local[b.ID] = blCALL
					certain[b.ID] = max(blCALL, certain[b.Succs[0].b.ID])
					break
				}
			}
		}
		if f.pass.debug > 2 {
			f.Warnl(b.Pos, "BP: Block %s, local=%s, certain=%s", b, bllikelies[local[b.ID]-blMin], bllikelies[certain[b.ID]-blMin])
		}

	}
}

func (l *loop) String() string {
	return fmt.Sprintf("hdr:%s", l.header)
}

func (l *loop) LongString() string {
	i := ""
	o := ""
	if l.isInner {
		i = ", INNER"
	}
	if l.outer != nil {
		o = ", o=" + l.outer.header.String()
	}
	return fmt.Sprintf("hdr:%s%s%s", l.header, i, o)
}

func (l *loop) isWithinOrEq(ll *loop) bool {
	if ll == nil { // nil means whole program
		return true
	}
	for ; l != nil; l = l.outer {
		if l == ll {
			return true
		}
	}
	return false
}

// nearestOuterLoop returns the outer loop of loop most nearly
// containing block b; the header must dominate b.  loop itself
// is assumed to not be that loop. For acceptable performance,
// we're relying on loop nests to not be terribly deep.
func (l *loop) nearestOuterLoop(sdom SparseTree, b *Block) *loop {
	var o *loop
	for o = l.outer; o != nil && !sdom.IsAncestorEq(o.header, b); o = o.outer {
	}
	return o
}

type loopBuilder struct {
	visited     []bool   // visited flag, indexed by block ID
	dfsp        []int32  // DFS spanning position, indexed by block ID
	iheader     []*Block // innermost loop header of block, indexed by block ID
	headers     []*Block // loop headers, may contain duplicates
	irreducible []bool   // irreducible loop headers, indexed by block ID
}

func (lb *loopBuilder) taggingHeader(b, h *Block) {
	if b == h || h == nil {
		return
	}
	cur1, cur2 := b, h
	for lb.iheader[cur1.ID] != nil {
		ih := lb.iheader[cur1.ID]
		if ih == cur2 {
			return
		}
		if lb.dfsp[ih.ID] < lb.dfsp[cur2.ID] {
			lb.iheader[cur1.ID] = cur2
			cur1 = cur2
			cur2 = ih
		} else {
			cur1 = ih
		}
	}
	lb.iheader[cur1.ID] = cur2
}

func (lb *loopBuilder) traverse(b0 *Block, DFSPPos int32) *Block {
	lb.visited[b0.ID] = true
	lb.dfsp[b0.ID] = DFSPPos
	// p: starting from h0, the path to b0(if b0 is traversed)
	for _, b := range b0.Succs {
		b := b.b // unwrap edge to get block
		if !lb.visited[b.ID] {
			// case a: b is not traversed, traverse it; if then b is found in
			// loop body, tag b's innermost loop header as b0's header
			nh := lb.traverse(b, DFSPPos+1)
			lb.taggingHeader(b0, nh)
			continue
		}
		// b is traversed, denote "p" as the current path from entry to b0
		if lb.dfsp[b.ID] > 0 {
			// case b: b is in p, tag b as b0's header
			lb.headers = append(lb.headers, b)
			lb.taggingHeader(b0, b)
		} else if lb.iheader[b.ID] == nil {
			// case c: b is not in p nor in loop body, do nothing
		} else {
			h := lb.iheader[b.ID] // h is b's innermost loop header
			if lb.dfsp[h.ID] > 0 {
				// case d: b is not in p but its innermost loop header h is in p
				// tag h as b0's header
				lb.taggingHeader(b0, h)
			} else {
				// case e, b is not in p and its innermost loop header h is not in p
				// mark h and its ancestors as irreducible because h is entered
				// from either b0 or its loop entry
				lb.irreducible[h.ID] = true
				for lb.iheader[h.ID] != nil {
					h = lb.iheader[h.ID]
					if lb.dfsp[h.ID] > 0 {
						lb.taggingHeader(b0, h)
						break
					}
					// mark loop h irreducible
					lb.irreducible[h.ID] = true
				}
			}
		}
	}
	lb.dfsp[b0.ID] = 0
	return lb.iheader[b0.ID]
}

func loopnestfor(f *Func) *loopnest {
	po := f.postorder()
	sdom := f.Sdom()
	b2l := make([]*loop, f.NumBlocks())
	loops := make([]*loop, 0)

	if f.pass.debug > 2 {
		fmt.Printf("loop finding in %s\n", f.Name)
	}

	lb := loopBuilder{
		visited:     f.Cache.allocBoolSlice(f.NumBlocks()),
		dfsp:        f.Cache.allocInt32Slice(f.NumBlocks()),
		iheader:     f.Cache.allocBlockSlice(f.NumBlocks()),
		headers:     make([]*Block, 0),
		irreducible: f.Cache.allocBoolSlice(f.NumBlocks()),
	}
	defer f.Cache.freeBoolSlice(lb.visited)
	defer f.Cache.freeInt32Slice(lb.dfsp)
	defer f.Cache.freeBlockSlice(lb.iheader)
	defer f.Cache.freeBoolSlice(lb.irreducible)

	// Traverse the CFG to find loop headers
	lb.traverse(f.Entry, 1) // Start with 1 so 0 means "not on stack"

	// Create loops
	seenHeaders := f.Cache.allocBoolSlice(f.NumBlocks())
	defer f.Cache.freeBoolSlice(seenHeaders)

	// Pre-allocate loops to ensure pointer stability if needed (though slice append is fine)
	loopMap := make([]*loop, f.NumBlocks())

	// Identify unique headers and create loop objects
	for _, h := range lb.headers {
		if !seenHeaders[h.ID] {
			seenHeaders[h.ID] = true
			l := &loop{header: h, isInner: true} // assume inner initially
			loops = append(loops, l)
			loopMap[h.ID] = l
		}
	}

	sawIrred := false
	for i, isIrred := range lb.irreducible {
		if isIrred {
			sawIrred = true
			// if we want to mark the loop object as irreducible, we can't currently (no field)
			// checking if we missed any headers that are irreducible but not reachable via backedge?
			// The algorithm marks h as irreducible. If h is a header, it should be in headers?
			// The algorithm only adds to headers in case b.
			// But case e marks h as irreducible.
			// If h was not found as a header via case b, it might not be in loops.
			// But for it to be in iheader, it must have been tagged.
		}
		_ = i
	}

	// Populate b2l and outer pointers
	for _, b := range f.Blocks {
		h := lb.iheader[b.ID]
		if seenHeaders[b.ID] {
			// b is a loop header.
			// Its outer loop is determined by iheader[b].
			l := loopMap[b.ID]
			b2l[b.ID] = l
			if h != nil {
				l.outer = loopMap[h.ID]
				if l.outer != nil {
					l.outer.isInner = false
				}
			}
		} else if h != nil {
			// b is inside loop headed by h
			l := loopMap[h.ID]
			b2l[b.ID] = l
		}
	}

	// Calculate nBlocks and depth
	for _, b := range f.Blocks {
		l := b2l[b.ID]
		if l != nil {
			l.nBlocks++
		}
	}

	for _, l := range loops {
		d := int16(1)
		for p := l.outer; p != nil; p = p.outer {
			d++
		}
		l.depth = d
	}

	ln := &loopnest{f: f, b2l: b2l, po: po, sdom: sdom, loops: loops, hasIrreducible: sawIrred}

	// Curious about the loopiness? "-d=ssa/likelyadjust/stats"
	if f.pass != nil && f.pass.stats > 0 && len(loops) > 0 {

		// Note stats for non-innermost loops are slightly flawed because
		// they don't account for inner loop exits that span multiple levels.

		for _, l := range loops {
			inner := 0
			if l.isInner {
				inner++
			}

			f.LogStat("loopstats in "+f.Name+":",
				l.depth, "depth",
				inner, "is_inner", l.nBlocks, "n_blocks")
		}
	}

	if f.pass != nil && f.pass.debug > 1 && len(loops) > 0 {
		fmt.Printf("Loops in %s:\n", f.Name)
		for _, l := range loops {
			fmt.Printf("%s, b=", l.LongString())
			for _, b := range f.Blocks {
				if b2l[b.ID] == l {
					fmt.Printf(" %s", b)
				}
			}
			fmt.Print("\n")
		}
		fmt.Printf("Nonloop blocks in %s:", f.Name)
		for _, b := range f.Blocks {
			if b2l[b.ID] == nil {
				fmt.Printf(" %s", b)
			}
		}
		fmt.Print("\n")
	}
	return ln
}

// depth returns the loop nesting level of block b.
func (ln *loopnest) depth(b ID) int16 {
	if l := ln.b2l[b]; l != nil {
		return l.depth
	}
	return 0
}
