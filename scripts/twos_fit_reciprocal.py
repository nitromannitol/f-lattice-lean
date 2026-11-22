"""Task 28: does pl.standard(2^k) equal a dihedral image, a translation and an affine term of the reciprocal field B1(d)?
Exact integer test on a window: r(x) = F(M x + t) - G(x) must be affine on the window (checked on all points)."""
import sys

import permit_local as pl
from twos_tools import DIHEDRAL, affine_on
from twos_tools import DIHEDRAL, affine_on


def search(k, d, R=6, T=10):
    F, _ = pl.standard(tuple([2] * k))
    G, _ = pl.standard(tuple([3] * ((d - 3) // 2)))
    window = [(x, y) for x in range(-R, R + 1) for y in range(-R, R + 1)]
    Gv = {z: G(z) for z in window}
    hits = []
    for M in DIHEDRAL:
        for tx in range(-T, T + 1):
            for ty in range(-T, T + 1):
                r = {}
                for z in window:
                    p = (M[0][0] * z[0] + M[0][1] * z[1] + tx, M[1][0] * z[0] + M[1][1] * z[1] + ty)
                    r[z] = F(p) - Gv[z]
                if affine_on(window, r):
                    hits.append((M, (tx, ty)))
                    return hits
    return hits


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    for k in range(1, kmax + 1):
        for d in (2 * k + 1, 2 * k + 3):
            h = search(k, d)
            print("2^%d vs B1(%d): %s" % (k, d, h if h else "no fit"))
