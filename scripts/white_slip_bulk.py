"""Task 33 (A): at non-free whites (non-port classes with lap 0), the slip-permitted inputs (D(a) <= D(y)) and the
bulk requirement: some slip-permitted input weakly lower in P and J (equal-level inputs handled by the same-level order).
Counts over all words, eta = +1 (sigma) and eta = -1 (-sigma)."""
import sys
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from arcs_check import e_rep
from exact_quotient import cut_on, words

def run(args):
    w, eta = args
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    F, _ = pl.standard(tuple(w))
    N, Dd = pl.parents(w)[0]
    sig = (eta * 2 * fr.eps * Dd, eta * 2 * fr.eps * N)
    D = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, eta)
    det, S0 = re_.cover_sites(K, V)
    n_white = n_one = n_none_weak = n_two = 0
    for r in S0:
        y = e_rep(fr, r)
        if lap(y) != 0:
            continue
        port = any(not fr.inE(q) for q in [(y[0]+1, y[1]), (y[0]-1, y[1]), (y[0], y[1]+1), (y[0], y[1]-1)])
        if port:
            continue
        n_white += 1
        ins = pl.neighbours(y)
        sp = [a for a in ins if D(a) <= D(y)]
        if len(sp) == 1:
            n_one += 1
        if len(sp) == 2:
            n_two += 1
        if not sp:
            n_none_weak += 1
            continue
        weak = [a for a in sp if P(a) <= P(y) and J(a) <= J(y)]
        if not weak:
            n_none_weak += 1
    return tuple(w), eta, n_white, n_one, n_two, n_none_weak

if __name__ == "__main__":
    ws = list(words(4))
    for eta in (1, -1):
        tot = dict(white=0, one=0, two=0, bad=0)
        with Pool(12) as pool:
            for w, e, nw, n1, n2, bad in pool.imap_unordered(run, [(w, eta) for w in ws]):
                tot["white"] += nw; tot["one"] += n1; tot["two"] += n2; tot["bad"] += bad
        print("ETA", eta, "NONFREE_WHITE_CLASSES", tot, flush=True)
