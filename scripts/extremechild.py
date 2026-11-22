"""Task 53 extreme-cell invariant, numerics: which copy supplies the extreme cells of the child's bottom and top rows.
For each non-base child (odd/even, phase): the child's bottom row (its minimum site row) and top row (maximum site row),
with the left and right site ends. For each end, the copies whose own bottom (top) row has the same end column after
their shift; the copy index is recorded when it is unique for every word of the class.
Usage: python3 extremechild.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words
from siterows import row_intervals


def ends(P, which):
    ri = row_intervals(P)
    y = min(ri) if which == "bottom" else max(ri)
    return y, ri[y][0], ri[y][1]


if __name__ == "__main__":
    L = int(sys.argv[1])
    res = {}
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            pieces = cs[kind]
            U = frozenset().union(*pieces)
            for which in ("bottom", "top"):
                y, l, r = ends(U, which)
                # copies attaining the same extreme end (left end at min x, right end at max x) on that row
                cand_l = []; cand_r = []
                for k, P in enumerate(pieces):
                    ri = row_intervals(P)
                    if y in ri:
                        if ri[y][0] == l: cand_l.append(k)
                        if ri[y][1] == r: cand_r.append(k)
                key = (kind, ph, which)
                c = res.setdefault(key, {"left": Counter(), "right": Counter(), "n": 0})
                c["n"] += 1
                c["left"][tuple(cand_l)] += 1
                c["right"][tuple(cand_r)] += 1
    for k in sorted(res):
        print(k, res[k]["n"], "left copies:", dict(res[k]["left"]), "right copies:", dict(res[k]["right"]))
