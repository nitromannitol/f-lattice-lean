"""Task 32 (d): the archive's free set = deck translates of the native boundary arcs of E (ALL_SLOPE line 21: 'E has
bottom H, left V, right U+V_i, top H_i+V, with four unit connectors and no additional lattice boundary sites').
Model: E = permit_local.Frame.inE (the fundamental window used by periodize). For each cover class we take its
E-representative y (the same reduction as periodize) and ask whether y lies on the lattice boundary of E (some
4-neighbour outside E). Compare the boundary classes with the forced free classes (a kept input raises P)."""
import sys
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, words

def e_rep(fr, z):
    a, b, c, h = pl.win((z[0] + z[1]) % 2 == 0, fr.n, fr.d)
    T = fr.T
    j = -((fr.t(z) - (a - T)) // T)
    i = (fr.sg(z) - c) // T
    y = (z[0] - i * fr.U[0] - j * fr.V[0], z[1] - i * fr.U[1] - j * fr.V[1])
    assert fr.inE(y), (z, y)
    return y

def run(w):
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    frm = pl.Frame(w)
    F, _ = pl.standard(tuple(w))
    P = cut_on(F, w, 1, 0, 1)
    det, S0 = re_.cover_sites(K, V)
    n, S0b, gP, lapv, eP, _ = build(K, V, lap, perm, P)
    _, _, _, _, eJ, _ = build(K, V, lap, perm, P)
    free_set = set()
    for p, z in enumerate(S0b):
        if any(pf and (gP[q] + wP - gP[p]) > 0 for (q, wP, pf) in eP[p]):
            free_set.add(p)
    # boundary classes: the E-representatives of the cover reps that lie on the lattice boundary of E
    bnd_set = set()
    for p, z in enumerate(S0b):
        y = e_rep(frm, z)
        nbrs = [(y[0] + 1, y[1]), (y[0] - 1, y[1]), (y[0], y[1] + 1), (y[0], y[1] - 1)]
        if any(not frm.inE(q) for q in nbrs):
            bnd_set.add(p)
    inter = free_set & bnd_set
    return tuple(w), n, len(free_set), len(bnd_set), len(inter), len(free_set - bnd_set), len(bnd_set - free_set)

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, free=0, bnd=0, inter=0, free_not_bnd=0, bnd_not_free=0)
    rows = []
    with Pool(12) as pool:
        for w, n, nf, nb, ni, fnb, bnf in pool.imap_unordered(run, ws):
            tot["classes"] += n; tot["free"] += nf; tot["bnd"] += nb; tot["inter"] += ni
            tot["free_not_bnd"] += fnb; tot["bnd_not_free"] += bnf
            rows.append((w, n, nf, nb, fnb, bnf))
    print("TOTAL", tot, flush=True)
    bad = [r for r in rows if r[4] or r[5]]
    print("WORDS_DIFFERENT", len(bad), flush=True)
    for r in sorted(bad, key=lambda r: (len(r[0]), r[0]))[:12]:
        print("WORD", r[0], "classes", r[1], "free", r[2], "bnd", r[3], "free_not_bnd", r[4], "bnd_not_free", r[5], flush=True)
