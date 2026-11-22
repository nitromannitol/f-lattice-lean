"""Task 53 (row invariant), numerics: are the site rows of the standard tiles intervals?
For each word w up to length L: the registers tO, tE after reading w (state(w)), the odd and even children, and
the standard tiles oddTile(w), evenTile(w). Reports the number of tiles with a site row that is not an interval.
Usage: python3 siterows.py L"""
import sys
from collections import Counter
from standard_tiles import state, words, oddTile, evenTile, childTiles


def row_intervals(T):
    r = {}
    for (x, y) in T:
        r.setdefault(y, []).append(x)
    out = {}
    for y, xs in r.items():
        xs = sorted(xs)
        ok = len(xs) == xs[-1] - xs[0] + 1
        out[y] = (xs[0], xs[-1], ok)
    return out


def nonconvex(T):
    return [y for y, (_, _, ok) in row_intervals(T).items() if not ok] if T else []


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    bad = []
    for w in words(L):
        par, tO, tE = state(w)
        for name, T in (("reg_tO", tO), ("reg_tE", tE), ("odd", oddTile(w)), ("even", evenTile(w))):
            cnt[name] += 1
            nc = nonconvex(T)
            if nc:
                cnt[name + "_nonconvex"] += 1
                if len(bad) < 5: bad.append((w, name, nc))
    print("words", L, dict(cnt))
    print("examples", bad)
