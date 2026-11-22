"""Task 28: the even standard field of 2^k (child (2k+1)/(2k+3) = rotate<1, 2k+2>) against the near-one even doubled
staircase of basecase_2k_even_std (NearOneBaseCases.paperNearLadderValue, d = 2k+2, tile (A u B u C) \\ D).
Exact integer test: F(M x + t) - V(x) affine on the tile points, for the dihedral maps M and translations t in a box."""
import sys

import permit_local as pl
from twos_tools import DIHEDRAL, affine_on


def in_A(d, x):
    return x in {(-1, 2 * d + 1), (d + 1, d - 1)}


def in_B(d, x):
    return x[1] - x[0] == d and 0 < x[0] < d


def in_C(d, x):
    return -1 <= x[0] <= d + 1 and 1 <= x[1] <= 3 * d - 1 and -1 <= x[1] - x[0] <= 2 * d + 1


def in_D(d, x):
    return (x[0] == -1 and x[1] <= d + 1) or (x[0] == d + 1 and x[1] >= 2 * d - 1)


def tile(d):
    pts = []
    for x1 in range(-1, d + 2):
        for x2 in range(1, 3 * d):
            x = (x1, x2)
            if (in_A(d, x) or in_B(d, x) or in_C(d, x)) and not in_D(d, x):
                pts.append(x)
    return pts


def ladder_value(d, x):
    ind = 1 if (in_A(d, x) or in_B(d, x)) else 0
    return (-((x[1] - x[0]) ** 2 // 4) + min(0, d - x[1]) + min(0, 2 * d - x[1])
            + max((x[1] - x[0]) - d, 0) + ind)


def search(k, T=8):
    d = 2 * k + 2
    F, _ = pl.standard(tuple([2] * k))
    pts = tile(d)
    V = {x: ladder_value(d, x) for x in pts}
    hits = []
    for M in DIHEDRAL:
        for tx in range(-T, T + 1):
            for ty in range(-T, T + 1):
                r = {}
                for x in pts:
                    p = (M[0][0] * x[0] + M[0][1] * x[1] + tx, M[1][0] * x[0] + M[1][1] * x[1] + ty)
                    r[x] = F(p) - V[x]
                if affine_on(pts, r):
                    hits.append((M, (tx, ty)))
    return len(pts), hits


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for k in range(1, kmax + 1):
        n, hits = search(k)
        print("2^%d (d=%d): tile points %d, fits: %s" % (k, 2 * k + 2, n, hits[:4] if hits else "none"))
