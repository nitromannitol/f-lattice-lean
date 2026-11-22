"""Task 54 numerics: do the copy attaining the minimum left end and the copy attaining the maximum right end of each
row of a child already cover the row (their intervals overlap or abut)? If so, a child row is the union of two copies.
Also checks the boundary-seam facts of task 54 on the odd and even children of words of length 1..L (2184 tiles at L=6).
Usage: python3 extremecover.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words
from siterows import row_intervals

if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        for kind in ("odd", "even"):
            pieces = cs[kind]
            rows = [row_intervals(P) for P in pieces]
            ys = set()
            for r in rows: ys |= set(r)
            ok = True
            for y in ys:
                present = [(k, rows[k][y][0], rows[k][y][1]) for k in range(6) if y in rows[k]]
                kl = min(present, key=lambda t: (t[1], t[0]))
                kr = max(present, key=lambda t: (t[2], -t[0]))
                lo, hi = kl[1], kr[2]
                a = (kl[1], kl[2]); b = (kr[1], kr[2])
                # the two extreme intervals cover [lo, hi] iff they overlap or abut
                if max(a[0], b[0]) > min(a[1], b[1]) + 1:
                    ok = False
            cnt[(kind, "two_extremes_cover_rows", ok)] += 1
    print(dict(cnt))
