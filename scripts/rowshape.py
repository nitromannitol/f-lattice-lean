"""Task 53 row invariant, numerics: shape of the row endpoints of the standard tiles.
For a tile with interval site rows, l(y) (left endpoint) and r(y) (right endpoint) over the rows y in [y0, y1]:
 - contiguous: the rows form a contiguous range of heights,
 - l is quasi-convex (nonincreasing then nondecreasing), r is quasi-concave (nondecreasing then nonincreasing).
Usage: python3 rowshape.py L"""
import sys
from collections import Counter
from standard_tiles import state, words, oddTile, evenTile
from siterows import row_intervals


def quasi_convex(v):
    # nonincreasing then nondecreasing
    i = 0
    while i + 1 < len(v) and v[i + 1] <= v[i]: i += 1
    return all(v[j + 1] >= v[j] for j in range(i, len(v) - 1))


def quasi_concave(v):
    return quasi_convex([-x for x in v])


def shape(T):
    ri = row_intervals(T)
    ys = sorted(ri)
    contiguous = ys == list(range(ys[0], ys[-1] + 1))
    l = [ri[y][0] for y in ys]; r = [ri[y][1] for y in ys]
    return contiguous, quasi_convex(l), quasi_concave(r)


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter(); bad = []
    for w in words(L):
        par, tO, tE = state(w)
        for name, T in (("tO", tO), ("tE", tE), ("odd", oddTile(w)), ("even", evenTile(w))):
            c, lc, rc = shape(T)
            cnt[(name, "tiles")] += 1
            cnt[(name, "contiguous")] += c
            cnt[(name, "l_quasi_convex")] += lc
            cnt[(name, "r_quasi_concave")] += rc
            if not (c and lc and rc) and len(bad) < 4: bad.append((w, name))
    for k in sorted(cnt): print(k, cnt[k])
    print("examples failing", bad)
