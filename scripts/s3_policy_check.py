"""Numerical check of the canonical S3 policy data (Lean: CanonicalPolicy in Plane/Induction/S3Canonical.lean), words <= 4.

For each proper word w (current frame of w, F = standard field of w, P = cutGrade 1 0 1, J = cutGrade 0 1 1 = rounded slip):
  * every site is reduced to a representative of the closed polygon E by deck shifts (kernel U = (d, n), transverse V);
  * black centres keep both inputs: each input must be permitted (slip increment <= 0) and weakly lower in (P, J);
  * white centres keep one input: a permitted input weakly lower in (P, J), strict drops preferred;
  * the policy is deck invariant (it is chosen on representatives).
The strict rank on equal-pair kept edges exists iff the graph of equal-pair kept edges on the representatives is acyclic
(a cycle of equal pairs lifts to a cycle of sites, and the pair fixes the lattice displacement).
Reports per word: non-permitted or non-monotone black inputs, white centres without a witness, equal-pair cycles.
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import cut_on, words


def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    fr = oc.frame(w)
    N, D, n, d, T, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"], fr["eps"]
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, 1)
    short = (2 * eps * D, 2 * eps * N)
    U = (d, n)
    V = (n - d, n + d)

    def perm(c, i):  # slipIncrement(F, F(.+sigma), c, i) <= 0
        def D1(z):
            return F(z) - F((z[0] + short[0], z[1] + short[1]))
        return D1(i) - D1(c) <= 0

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
        z2 = (z1[0] + a * U[0], z1[1] + a * U[1])
        assert oc.in_polygon(z2, fr), (w, z, z2)
        return z2

    x0, x1, y0, y1 = oc.window(fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if oc.in_polygon((x, y), fr)]
    stats = defaultdict(int)
    graph = {r: [] for r in reps}
    for r in reps:
        lv = pl.lap(F, r)
        stats["centres"] += 1
        ins = [oc.incoming_neg(r), oc.incoming_pos(r)]
        info = []
        for i in ins:
            dP = P(i) - P(r)
            dJ = J(i) - J(r)
            info.append((i, dP, dJ, perm(r, i)))
        if lv == -1:
            stats["black"] += 1
            for (i, dP, dJ, pf) in info:
                if not pf:
                    stats["black_not_permitted"] += 1
                if not (dP <= 0 and dJ <= 0):
                    stats["black_not_monotone"] += 1
            for (i, dP, dJ, pf) in info:
                if dP == 0 and dJ == 0:
                    graph[r].append(reduce(i))
        else:
            stats["white"] += 1
            cand = [(i, dP, dJ) for (i, dP, dJ, pf) in info if pf and dP <= 0 and dJ <= 0]
            if not cand:
                stats["white_no_witness"] += 1
                continue
            strict = [c for c in cand if c[1] < 0 or c[2] < 0]
            if strict:
                stats["white_strict_witness"] += 1
                continue
            stats["white_equal_only"] += 1
            graph[r].append(reduce(cand[0][0]))
    # cycle test on equal-pair edges (Kahn)
    indeg = defaultdict(int)
    for r in reps:
        for s in graph[r]:
            indeg[s] += 1
    queue = [r for r in reps if indeg[r] == 0]
    seen = 0
    while queue:
        r = queue.pop()
        seen += 1
        for s in graph[r]:
            indeg[s] -= 1
            if indeg[s] == 0:
                queue.append(s)
    stats["cycle_nodes"] = len(reps) - seen
    return tuple(w), dict(stats), len(reps)


if __name__ == "__main__":
    ws = list(words(4))
    tot = defaultdict(int)
    bad_words = []
    with Pool(12) as pool:
        for w, st, nreps in pool.imap_unordered(run, ws):
            for k, v in st.items():
                tot[k] += v
            tot["reps"] += nreps
            if st.get("black_not_permitted", 0) or st.get("black_not_monotone", 0) or st.get("white_no_witness", 0) or st.get("cycle_nodes", 0):
                bad_words.append((w, {k: v for k, v in st.items() if v}))
    print("TOTAL", dict(tot), flush=True)
    print("BAD WORDS", len(bad_words), bad_words[:6], flush=True)
