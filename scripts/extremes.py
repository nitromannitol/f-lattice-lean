"""Task 53 extreme-cell invariant, numerics: for each register tile T(f) (the tile of a parent fraction f = (num, den)),
the height H (top row), the bottom row's site interval [b0, b1] and the top row's site interval [t0, t1].
Register tiles are determined by their fraction (checked).  Usage: python3 extremes.py L"""
import sys
from collections import defaultdict
from standard_tiles import state, words
from siterows import row_intervals


def tile_table(L):
    tab = {}
    for w in words(L):
        par, tO, tE = state(w)
        for T, f in ((tO, par[0]), (tE, par[1])):
            tab.setdefault(f, frozenset(T))
    return tab


def extremes(T):
    ri = row_intervals(T)
    ys = sorted(ri)
    H = ys[-1]
    b0, b1 = ri[ys[0]][0], ri[ys[0]][1]
    t0, t1 = ri[H][0], ri[H][1]
    return ys[0], H, (b0, b1), (t0, t1)


if __name__ == "__main__":
    L = int(sys.argv[1])
    tab = tile_table(L)
    rows = []
    for f in sorted(tab, key=lambda f: (f[1], f[0])):
        y0, H, bot, top = extremes(tab[f])
        rows.append((f, y0, H, bot, top))
    for r in rows: print(r)
