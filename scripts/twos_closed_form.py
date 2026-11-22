"""Task 28: is the standard field of 2^k a near-one or reciprocal base field, up to a dihedral map, a translation and an
affine term? Compares pl.standard(2^k) with the TeX near-one staircase values (NearOneBaseCases.paperNearStairValue,
d odd) and with the reciprocal field B1(d) on sample windows, for k = 1..5."""
import itertools
import sys

import permit_local as pl
from twos_tools import DIHEDRAL, affine_on


def near_stair_value(d, x):
    # paperNearStairValue d x = -((x2 - x1)^2 / 4) + min(d - x2, 0) + [x = (0, d+1) or (d+1, d-1)]
    v = -(((x[1] - x[0]) ** 2) // 4) + min(d - x[1], 0)
    if x == (0, d + 1) or x == (d + 1, d - 1):
        v += 1
    return v


def tile_points(d):
    return [(x, y) for x in range(0, d + 2) for y in range(1, 2 * d) if -1 <= y - x <= d]


def fit_search(k, dmax_shift=8):
    w = tuple([2] * k)
    F, _ = pl.standard(w)
    res = []
    for d in (2 * k + 1, 2 * k + 3):
        pts = tile_points(d)
        if len(pts) < 10:
            continue
        for M in DIHEDRAL:
            for tx in range(-dmax_shift, dmax_shift + 1):
                for ty in range(-dmax_shift, dmax_shift + 1):
                    # compare F at M x + t with the near-one value at x (tile coordinates)
                    vals = []
                    ok = True
                    rr = []
                    for x in pts:
                        p = (M[0][0] * x[0] + M[0][1] * x[1] + tx, M[1][0] * x[0] + M[1][1] * x[1] + ty)
                        rr.append(F(p) - near_stair_value(d, x))
                    if affine_on(pts, dict(zip(pts, rr))):
                        res.append((d, M, (tx, ty)))
                        break
    return res


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for k in range(1, kmax + 1):
        hits = fit_search(k)
        print("2^%d near-one fits:" % k, hits[:3] if hits else "none")
