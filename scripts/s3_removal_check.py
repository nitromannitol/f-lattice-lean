"""Task 58 (c): the Q1 removal lists at the fixed pair (c0, 0) against the prescribed kept edges (eta = +1), words <= 4.

Level sites: each free representative of s3_free_check.py (H_j, V_j) has one translate at the fixed pair (c0, 0), with
  H_j + i U  -> H_{j + d i},   i = P(z) - c0,
  V_k + j V  -> V_{k + L j},   j = -J(z)            (V_{k+L} = V_k + V).
c0 = P(H_0).  Rows tested:
  'minus' as printed in Q1:   V_r..V_1, H_0, V_0, H_{-1}..H_{1-d}, V_{-1}..V_{r+1-L}
  'plus'  as printed in Q1:   V_{-r-1}..V_{-1}, H_0, V_0, V_1..V_{L-r-2}, H_{-1}..H_{1-d}
  'minus-mirror' (hypothesis): V_{L-r-2}..V_1, H_0, V_0, H_{-1}..H_{1-d}, V_{-1}..V_{-r-1}
Checks: (i) the level labels are exactly the labels of the row; (ii) for every level site whose prescribed kept
target is a free level site, the target occurs earlier in the row.
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import cut_on, words
from s3_free_check import EAST, NORTH, SOUTH


def list_labels(row, r, d, n):
    L = d + n
    Hneg = [("H", h) for h in range(-1, -d, -1)]
    if row == "minus":
        return [("V", v) for v in range(r, 0, -1)] + [("H", 0), ("V", 0)] + Hneg + \
               [("V", v) for v in range(-1, r - L, -1)]
    if row == "plus":
        return [("V", v) for v in range(-r - 1, 0)] + [("H", 0), ("V", 0)] + \
               [("V", v) for v in range(1, L - r - 1)] + Hneg
    if row == "minus-mirror":
        return [("V", v) for v in range(L - r - 2, 0, -1)] + [("H", 0), ("V", 0)] + Hneg + \
               [("V", v) for v in range(-1, -r - 2, -1)]
    raise ValueError(row)


def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    fr = oc.frame(w)
    N, D, n, d, T, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"], fr["eps"]
    L = n + d
    r = D + N
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, 1)
    U, V = (d, n), (n - d, n + d)

    def tg(z):
        return n * z[0] - d * z[1]

    def sg(z):
        return (d + n) * z[0] + (d - n) * z[1]

    def reduce(z):
        even = oc.even_site(z)
        tlo = 2 - T if even else n - T
        slo = 0 if even else 2 - d + n
        b = (tg(z) - tlo) // T
        z1 = (z[0] + b * V[0], z[1] + b * V[1])
        a = -((sg(z1) - slo) // T)
        return (z1[0] + a * U[0], z1[1] + a * U[1])

    x0, x1, y0, y1 = oc.window(fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if oc.in_polygon((x, y), fr)]
    inE = lambda z: oc.in_polygon(z, fr)
    Hspec = set(range(2, L - 1, 2)) | set(range(n, d + 1, 2))
    Vspec = set(range(0, 2 * n + 1, 2)) | set(range(2 - d + n, L - 1, 2))
    Hb = sorted((z for z in reps if not inE((z[0], z[1] - 1)) and tg(z) in Hspec), key=lambda z: z[0])
    Vb = sorted((z for z in reps if not inE((z[0] - 1, z[1])) and sg(z) in Vspec), key=lambda z: z[1])
    c0 = P(Hb[0])
    free = {}
    for j, z in enumerate(Hb):
        free[z] = ("H", j)
    for k, z in enumerate(Vb):
        free[z] = ("V", k)
    label_of = {}
    level = {}
    for rep, (kind, j) in free.items():
        i = P(rep) - c0
        jj = -J(rep)
        lam = (rep[0] + i * U[0] + jj * V[0], rep[1] + i * U[1] + jj * V[1])
        assert P(lam) == c0 and J(lam) == 0
        lab = ("H", j + d * i) if kind == "H" else ("V", j + L * jj)
        label_of[rep] = lab
        level[lam] = rep

    def presc(rep):
        kind, j = free[rep]
        if kind == "H":
            if j == 0:
                return SOUTH          # -eta north, eta = +1
            if j == d - 1:
                return NORTH
            return EAST if oc.even_site(rep) else NORTH
        if j == 0 or j == L - 1:
            return EAST               # V_0: east; V_{L-1}: eta east
        return EAST if oc.even_site(rep) else SOUTH

    pairs = []
    for lam, rep in level.items():
        dv = presc(rep)
        tgt = (lam[0] + dv[0], lam[1] + dv[1])
        assert tgt in (oc.incoming_neg(lam), oc.incoming_pos(lam))
        rt = reduce(tgt)
        if rt in free and P(tgt) == c0 and J(tgt) == 0:
            pairs.append((label_of[rep], label_of[rt]))
        else:
            pairs.append((label_of[rep], None))
    labels = set(label_of.values())
    out = {}
    for row in ("minus", "plus", "minus-mirror"):
        seq = list_labels(row, r, d, n)
        pos = {lab: k for k, lab in enumerate(seq)}
        same = labels == set(seq)
        bad = sum(1 for a, b in pairs if b is not None and (b not in pos or a not in pos or not pos[b] < pos[a]))
        out[row] = (same, bad)
    return tuple(w), out, (n, d, L, r)


if __name__ == "__main__":
    ws = list(words(4))
    stats = defaultdict(int)
    with Pool(12) as pool:
        for w, out, (n, d, L, r) in pool.imap_unordered(run, ws):
            for row, (same, bad) in out.items():
                stats[(row, "labels equal" if same else "labels differ")] += 1
                stats[(row, "order violations", bad)] += 0
                if same and bad == 0:
                    stats[(row, "consistent")] += 1
                if same:
                    stats[(row, "sum violations")] += bad
            stats[("L == 2r+2", L == 2 * r + 2)] += 1
    for k in sorted(stats, key=str):
        if stats[k]:
            print(k, stats[k])
