"""Task 53 row invariant, numerics: two conditions that reduce the child's row-chain property to its copies.
 (V) vertical: the child's cell rows are covered without holes by the copies' cell-row ranges: every consecutive pair
     (y, y+1) of child cell rows lies inside the cell-row range of one copy (copies are row chains, so that copy then
     overlaps the child's rows y and y+1).
 (H) horizontal: in every site row, the copies present have pairwise abutting or overlapping site intervals.
Usage: python3 childcond.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words, cellTile
from siterows import row_intervals


def cell_rows(T):
    ys = {}
    for (x, y) in T: ys.setdefault(y, []).append(x)
    return sorted(ys)


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    ex = []
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            pieces = cs[kind]
            cnt[(kind, ph, "n")] += 1
            # (V)
            U = cellTile(frozenset().union(*pieces))
            child_rows = cell_rows(U)
            crange = [cell_rows(cellTile(P)) for P in pieces]
            pair_ok = True
            if child_rows:
                for y in range(min(child_rows), max(child_rows)):
                    if not any(r and min(r) <= y and y + 1 <= max(r) for r in crange):
                        pair_ok = False; break
            cnt[(kind, ph, "V_pairs_covered")] += pair_ok
            # (H): pairwise abut of site intervals in every row
            rows = [row_intervals(P) for P in pieces]
            H_ok = True
            ys = set()
            for ri in rows: ys |= set(ri)
            for y in ys:
                iv = [(ri[y][0], ri[y][1]) for ri in rows if y in ri]
                for i in range(len(iv)):
                    for j in range(i + 1, len(iv)):
                        a, b = iv[i], iv[j]
                        if max(a[0], b[0]) > min(a[1], b[1]) + 1:
                            H_ok = False
            cnt[(kind, ph, "H_pairwise_abut")] += H_ok
    for k in sorted(cnt): print(k, cnt[k])
