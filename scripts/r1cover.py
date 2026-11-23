"""Task 55 (R1) numerics: the covering comparisons per child type.

For a non-base word w (not empty, not all 2, not all 3), the odd child and the even child are unions of six pieces, each a
register tile (tO or tE) shifted by an offset built from texV1Odd(p), texV1Even(q), texV2(p), texV2(q) (standard_tiles.py,
oddChildB / evenChildB). Per child row y, the pieces meet along the row. This script checks, for every such word of length
1..L:
  (a) the pieces are pairwise disjoint and their union is the child (cell sets);
  (b) on each row, each piece's cells form an interval;
  (c) for the pieces ordered by their left end on row y, consecutive pieces abut (right end = next left end), overlap or
      leave a gap.
It tallies, per child type and per pair of piece indices (i, j) that are consecutive on a row, the number of abutments,
overlaps and gaps. A pair with only abutments is a needed comparison: R_piece_i(y) = L_piece_j(y).
Usage: python3 r1cover.py L"""
import sys
from collections import Counter, defaultdict
from standard_tiles import (words, shift, add, texV1Odd, texV1Even, texV2, oddTile, evenTile, state,
                            childTiles, nstairN, stairF, ladderF, nladderN)

ZERO = (0, 0)


def pieces_odd(b, T1, T2, p, q):
    """The six pieces of oddChildB as (tile, offset) pairs, in the order of the Lean definition."""
    if b:
        return [(T2, texV1Odd(p)), (T2, add(texV1Odd(p), texV1Even(q))), (T2, texV2(p)),
                (T2, add(texV2(p), texV1Even(q))), (T1, ZERO),
                (T1, add(add(texV1Even(q), texV1Even(q)), texV2(q)))]
    return [(T2, ZERO), (T2, texV1Even(q)), (T2, add(texV1Odd(p), texV2(p))),
            (T2, add(add(texV1Odd(p), texV2(p)), texV1Even(q))),
            (T1, add(texV1Even(q), texV1Even(q))), (T1, texV2(q))]


def pieces_even(b, T1, T2, p, q):
    """The six pieces of evenChildB as (tile, offset) pairs."""
    if b:
        return [(T2, texV1Odd(p)), (T2, add(texV2(p), texV2(p))), (T1, ZERO), (T1, texV2(p)),
                (T1, add(texV1Even(q), texV2(q))), (T1, add(add(texV1Even(q), texV2(q)), texV2(p)))]
    return [(T2, ZERO), (T2, add(texV1Odd(p), add(texV2(p), texV2(p)))), (T1, texV1Even(q)),
            (T1, add(texV1Even(q), texV2(p))), (T1, texV2(q)), (T1, add(texV2(q), texV2(p)))]


def cells(tile, off):
    return frozenset(shift(tile, off))


def row_intervals(S, y):
    """For the cell set S, the cells on row y as a sorted list of x values."""
    return sorted(x for (x, yy) in S if yy == y)


def analyse_child(pieces, child, stats, kind):
    sets = [cells(t, o) for (t, o) in pieces]
    union = frozenset().union(*sets)
    stats[(kind, "union_is_child")] += 1 if union == frozenset(child) else 0
    stats[(kind, "union_total")] += 1
    ys = sorted({y for (_, y) in union})
    for y in ys:
        rows = []
        for i, s in enumerate(sets):
            xs = row_intervals(s, y)
            if not xs:
                continue
            stats[(kind, "row_interval")] += 1 if xs == list(range(xs[0], xs[-1] + 1)) else 0
            stats[(kind, "row_total")] += 1
            rows.append((xs[0], xs[-1] + 1, i))
        rows.sort()
        # coverage of the child row by the piece intervals: contiguous (no gap) and the ends
        reach = rows[0][1]
        gap = False
        for (l, r, i) in rows[1:]:
            if l > reach:
                gap = True
            reach = max(reach, r)
        stats[(kind, "row_contiguous")] += 0 if gap else 1
        stats[(kind, "row_total2")] += 1
        Lmin = min(l for (l, r, i) in rows)
        Rmax = max(r for (l, r, i) in rows)
        left_pieces = tuple(sorted(i for (l, r, i) in rows if l == Lmin))
        right_pieces = tuple(sorted(i for (l, r, i) in rows if r == Rmax))
        stats[(kind, "left_end", left_pieces)] += 1
        stats[(kind, "right_end", right_pieces)] += 1


def main(L):
    stats = Counter()
    words_checked = 0
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w):
            continue
        par, tO, tE = state(w)
        p, q = par
        phase_b = sum(1 for x in w if x == 1) % 2 == 1
        child_odd, child_even = childTiles(w, par, tO, tE)
        analyse_child(pieces_odd(phase_b, tO, tE, p, q), child_odd, stats, "odd")
        analyse_child(pieces_even(phase_b, tO, tE, p, q), child_even, stats, "even")
        words_checked += 1
    print("words checked:", words_checked)
    for kind in ("odd", "even"):
        print(f"== {kind} child")
        print("  union is child:", stats[(kind, "union_is_child")], "/", stats[(kind, "union_total")])
        print("  each piece's row is an interval:", stats[(kind, "row_interval")], "/", stats[(kind, "row_total")])
        print("  rows contiguous (no gap in the covering):", stats[(kind, "row_contiguous")], "/", stats[(kind, "row_total2")])
        for end in ("left_end", "right_end"):
            keys = sorted({k for k in stats if k[0] == kind and k[1] == end}, key=lambda k: -stats[k])
            for k in keys:
                print("  ", end, "attained by pieces", k[2], ":", stats[k])


if __name__ == "__main__":
    main(int(sys.argv[1]))
