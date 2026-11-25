"""H-price deck identities of the note (H_PRICE_VS_PINGPONG_E §W0/W1; H_SOURCE §3-4), over u in words(4):
  A(z) = FqW(z - lv) = 0 on the word's free H trace;  Psi(z + Vp) = Psi(z) - 1 for z on the trace, Vp = (N-D, N+D).
Same sheet formulas as w1_psi_check.py."""
import sys
sys.path.insert(0, 'scripts'); sys.path.insert(0, 'scripts')
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
    G, _ = pl.standard(tuple(cw))
    def FqW(z):
        return G((-z[1], z[0] - 1)) + harmonic(z)
    def A(z):
        return FqW((z[0] - lv[0], z[1] - lv[1]))
    def Psi(z):
        zl = (z[0] - lv[0], z[1] - lv[1])
        return FqW((zl[0] - te[0], zl[1] - te[1])) + (nq * zl[0] - dq * zl[1]) + ce - A(z)
    fr = Frame(n, d)
    H = []
    for x in range(1, d + 1):
        ys = [y for y in range(-3 * fr.L - 3 * fr.T - 5, 3 * fr.L + 3 * fr.T + 5) if fr.freeH((x, y))]
        H.append((x, ys[0]))
    a_zero = all(A(z) == 0 for z in H)
    deck = all(Psi((z[0] + Vp[0], z[1] + Vp[1])) == Psi(z) - 1 for z in H)
    return u, a_zero, deck

if __name__ == '__main__':
    tot = Counter(); bad = []
    with Pool(8) as pool:
        for u, a, dk in pool.imap_unordered(job, list(eq.words(4))):
            tot[('A=0 on H trace', a)] += 1
            tot[('Psi(z+Vp)=Psi(z)-1 on H trace', dk)] += 1
            if not (a and dk): bad.append((u, a, dk))
    for k in sorted(tot, key=str): print(k, tot[k])
    print('failing words:', bad[:6])
