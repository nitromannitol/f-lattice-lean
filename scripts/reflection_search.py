"""Search for the reflection behind the eps = -1 branch of (I2) (archive: 'handled by reflection').

For each proper word w (116 words, length <= 4) and each candidate affine map R(z) = M z + t of Z^2, test whether the
sheet differences Psi = C - A (Lean sheetC - sheetA) and the sheets themselves satisfy one of the identities

   (a) Psi(R z) = s Psi(z) + c              (s = +1 or -1; the reflection of the difference)
   (b) A(R z)   = C(z) + c   and  C(R z) = A(z) + c       (the sheets exchanged, a reflection that swaps strict sheets)
   (c) A(R z)   = A(z) + c   and  C(R z) = C(z) + c       (a symmetry of each sheet)

on every site z of a window around E (the window of open_inputs_check), with one constant c per identity.
Candidates M: the eight integer matrices of the dihedral group of the square; t: a small set built from the child
(U = (d, n), I = (1, -1), the zero and the H corner points). A candidate that holds exactly on a word is reported.

Output: for each eps (the sign of the word), the candidates that hold on all words of that eps, and for each candidate
the number of words it fails on. Exact integer equality is required; nothing is inferred from samples.
"""
import sys
from collections import Counter

import open_inputs_check as oc
import permit_local as pl

DIHEDRAL = [
    ((1, 0), (0, 1)), ((-1, 0), (0, 1)), ((1, 0), (0, -1)), ((-1, 0), (0, -1)),
    ((0, 1), (1, 0)), ((0, -1), (1, 0)), ((0, 1), (-1, 0)), ((0, -1), (-1, 0)),
]


def apply(M, z):
    return (M[0][0] * z[0] + M[0][1] * z[1], M[1][0] * z[0] + M[1][1] * z[1])


def translations(fr):
    d, n = fr["d"], fr["n"]
    cands = {
        "0": (0, 0), "I": (1, -1), "U": (d, n), "U+I": (d + 1, n - 1), "U-I": (d - 1, n + 1),
        "(d,0)": (d, 0), "(0,n)": (0, n), "-I": (-1, 1), "-U": (-d, -n),
    }
    return cands


def window_points(fr):
    x0, x1, y0, y1 = oc.window(fr)
    pts = []
    for x in range(x0 - 2, x1 + 3):
        for y in range(y0 - 2, y1 + 3):
            pts.append((x, y))
    return pts


def search(w, pts_cache=None):
    Fp, Xi, off = pl.model(w)
    fr = oc.frame(w)
    shift, offset, const = fr["shift"], fr["offset"], fr["constant"]
    nq, dq = fr["nq_"], fr["dq_"]

    def A(z):
        return Fp((z[0] - shift[0], z[1] - shift[1]))

    def C(z):
        x = (z[0] - shift[0], z[1] - shift[1])
        return Fp((x[0] - offset[0], x[1] - offset[1])) + (nq * x[0] - dq * x[1]) + const

    pts = window_points(fr)
    Av = {z: A(z) for z in pts}
    Cv = {z: C(z) for z in pts}
    Ps = {z: Cv[z] - Av[z] for z in pts}
    found = []
    trans = translations(fr)
    for mi, M in enumerate(DIHEDRAL):
        for tname, t in trans.items():
            R = lambda z, M=M, t=t: (apply(M, z)[0] + t[0], apply(M, z)[1] + t[1])
            images = {}
            ok = True
            for z in pts:
                r = R(z)
                if r not in Av:
                    ok = False
                    break
                images[z] = r
            if not ok:
                continue
            # (a) Psi(Rz) = s Psi(z) + c
            for s in (1, -1):
                diffs = {Ps[images[z]] - s * Ps[z] for z in pts}
                if len(diffs) == 1:
                    found.append(("a", mi, tname, s, diffs.pop()))
            # (b) sheets exchanged
            dA = {Av[images[z]] - Cv[z] for z in pts}
            dC = {Cv[images[z]] - Av[z] for z in pts}
            if len(dA) == 1 and len(dC) == 1:
                found.append(("b", mi, tname, dA.pop(), dC.pop()))
            # (c) each sheet symmetric
            dA2 = {Av[images[z]] - Av[z] for z in pts}
            dC2 = {Cv[images[z]] - Cv[z] for z in pts}
            if len(dA2) == 1 and len(dC2) == 1:
                found.append(("c", mi, tname, dA2.pop(), dC2.pop()))
    return fr["eps"], found


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    words = list(pl.proper_words(maxlen))
    per_eps = {1: Counter(), -1: Counter()}
    counts = {1: 0, -1: 0}
    for w in words:
        eps, found = search(w)
        counts[eps] += 1
        for item in set(found):
            key = (item[0], item[1], item[2], item[3]) if item[0] == "a" else (item[0], item[1], item[2])
            per_eps[eps][key] += 1
    for eps in (1, -1):
        print("eps", eps, "words", counts[eps])
        for key, cnt in per_eps[eps].most_common(12):
            print("   candidate", key, "holds on", cnt, "words")
