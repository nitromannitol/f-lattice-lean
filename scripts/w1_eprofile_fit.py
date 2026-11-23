"""H_PRICE check (task 118): the outgoing E profile of H_PRICE_VS_PINGPONG_E with the word's own standard field F_u (its child is q0),
a_p = (N, -D), c_p = -(T_p + L_p)/2 (W0), Vp = (N-D, N+D). Claims checked on every free H point z of the word u (u in words(4)):
  W0: E(z) = F_u(z+Vp) - a_p.z - c_p = 1 + min(0, Psi(z) - 1);  E(H_0) = 0 (anchor), c_p = -(T_p+L_p)/2 holds;
  W1: E(w) = F_u(w+Vp) - a_p.w - c_p = min(0, Psi(w) - 1) with c_p solved at the point Psi = 0 (H_last).
Plus F_u(z) = 0 on the trace (P = c0 - E needs it) and Psi(z+Vp) = Psi(z) - 1 (w1_price_check.py)."""
import sys
sys.path.insert(0, 'scripts'); sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w3/scripts')
from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import open_inputs_check as oc
import exact_quotient as eq
import w1_pinned_edges as PE
from w1_arc_prescription import F as Frame
from w1_psi_check import harmonic

def job(u):
    cw = PE.conj_of(u)
    fu = oc.frame(list(u))
    eps, n, d, nq, dq, N, D = fu['eps'], fu['n'], fu['d'], fu['nq'], fu['dq'], fu['N'], fu['D']
    lv, te, ce = fu['shift'], fu['offset'], fu['constant']
    Vp = (N - D, N + D)
    a = (N, -D)
    Tp, Lp = D * D + 2 * D * N - N * N, N + D
    G, _ = pl.standard(tuple(cw))
    Fu, _ = pl.standard(tuple(u))
    def FqW(z): return G((-z[1], z[0] - 1)) + harmonic(z)
    def Psi(z):
        zl = (z[0] - lv[0], z[1] - lv[1])
        return FqW((zl[0] - te[0], zl[1] - te[1])) + (nq * zl[0] - dq * zl[1]) + ce - FqW(zl)
    fr = Frame(n, d)
    H = []
    for x in range(1, d + 1):
        ys = [y for y in range(-3 * fr.L - 3 * fr.T - 5, 3 * fr.L + 3 * fr.T + 5) if fr.freeH((x, y))]
        H.append((x, ys[0]))
    W = (1 + eps) // 2
    Fz0 = all(Fu(z) == 0 for z in H)
    dk = all(Psi((z[0] + Vp[0], z[1] + Vp[1])) == Psi(z) - 1 for z in H)
    Fv = {z: Fu((z[0] + Vp[0], z[1] + Vp[1])) for z in H}
    if W == 0:
        target = {z: 1 + min(0, Psi(z) - 1) for z in H}
        anchor = H[0]
    else:
        target = {z: min(0, Psi(z) - 1) for z in H}
        anchor = [z for z in H if Psi(z) == 0][0]
    c = Fv[anchor] - a[0] * anchor[0] - a[1] * anchor[1] - target[anchor]
    fit = all(Fv[z] - a[0] * z[0] - a[1] * z[1] - c == target[z] for z in H)
    cok = (c == -(Tp + Lp) // 2) if W == 0 else None
    return u, W, Fz0, dk, fit, cok

if __name__ == '__main__':
    tot = Counter()
    with Pool(8) as pool:
        for u, W, Fz0, dk, fit, cok in pool.imap_unordered(job, list(eq.words(4))):
            tot[('W%d' % W, 'F_u=0 on trace', Fz0)] += 1
            tot[('W%d' % W, 'Psi(z+Vp)=Psi(z)-1', dk)] += 1
            tot[('W%d' % W, 'E profile fits', fit)] += 1
            if W == 0: tot[('W0', 'c_p = -(Tp+Lp)/2', cok)] += 1
    for k in sorted(tot, key=str): print(k, tot[k])
