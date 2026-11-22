"""Task 53 row invariant, numerics: where the extreme copy switches along the rows of a child.
For each non-base word, child kind and phase: the rows where the left (or right) extreme copy changes, and whether each
switch height is the bottom or top row of one of the copies (its own row range). Also records the bottom and top rows of
the child and of each copy. Usage: python3 rowswitch.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words
from rowcopies import analyse
from siterows import row_intervals

if __name__ == "__main__":
    L = int(sys.argv[1])
    res = {}
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            pieces = cs[kind]
            rows = analyse(pieces)
            ys = sorted(rows)
            ends = set()
            for P in pieces:
                ri = row_intervals(P)
                if ri:
                    ends.add(min(ri)); ends.add(max(ri))
            for role, idx in (("lmin", 1), ("rmax", 2)):
                c = res.setdefault((kind, ph, role), Counter())
                for i in range(len(ys) - 1):
                    a, b = ys[i], ys[i + 1]
                    if rows[a][idx] != rows[b][idx]:
                        # switch between row a and row b: the new block starts at b
                        c["switches"] += 1
                        c["switch at a copy end" if (b in ends or a in ends) else "switch NOT at copy end"] += 1
                c["words"] += 1
    for k in sorted(res):
        print(k, dict(res[k]))
