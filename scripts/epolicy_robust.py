"""Task 33 (A), classification-free part: the e-policy keeps BOTH inputs at black classes and at non-free whites.
Counts over all classes (E representatives), eta = +1 (slip with sigma) and eta = -1 (slip with -sigma):
  slip: kept pairs with D(input) > D(center)   (D = F - F(.+eta sigma))
  P/J : kept pairs (both inputs) with P or J increasing, split by black/white
Free ports are NOT used here (their prescribed input depends on the arc classification, which the model cannot yet fix)."""
import sys
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from arcs_check import e_rep
from exact_quotient import cut_on

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
    out = dict(black=0, white=0, slip_black=0, slip_white=0, P_black=0, P_white=0, J_black=0, J_white=0,
               slipperm_fail_white=0, port_white=0)
    for r in S0:
        y = e_rep(fr, r)
        l = lap(y)
        port = any(not fr.inE(q) for q in [(y[0]+1, y[1]), (y[0]-1, y[1]), (y[0], y[1]+1), (y[0], y[1]-1)])
        if port and l == 0:
            out["port_white"] = out.get("port_white", 0) + 1
            continue
        key = "black" if l == -1 else "white"
        out[key] += 1
        for a in pl.neighbours(y):
            if D(a) > D(y):
                out["slip_" + key] += 1
            if P(a) > P(y):
                out["P_" + key] += 1
            if J(a) > J(y):
                out["J_" + key] += 1
        if l == 0:
            # S3 slip permits at a white: are both inputs slip-permitted (needed if both are kept)?
            both = all(D(a) <= D(y) for a in pl.neighbours(y))
            if not both:
                out["slipperm_fail_white"] += 1
    return tuple(w), out

if __name__ == "__main__":
    from exact_quotient import words
    ws = list(words(4))
    eta = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    tot = dict(black=0, white=0, port_white=0, slip_black=0, slip_white=0, P_black=0, P_white=0, J_black=0, J_white=0, slipperm_fail_white=0)
    with Pool(12) as pool:
        for w, o in pool.imap_unordered(run, [(w, eta) for w in ws]):
            for k in tot:
                tot[k] += o[k]
    print("ETA", eta, "TOTAL", tot, flush=True)
