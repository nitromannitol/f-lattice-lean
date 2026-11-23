"""For each word u in words(4): eta = eps(u); the conjugate cw = conjWord(u) with frame eps_c.
(a) the three pins of the note under eta = eps(u) on the conjugate's canonical rule (as w1_pinned_edges.check);
(b) Psi on the word's H trace: Psi = C - A with A(z) = FqW(z - lv), C(z) = FqW(z - lv - te) + aq.(z - lv) + c_e,
    FqW = quarterTurnField(standard(cw)): FqW(z) = G(zTurn z) + harmonicGrid z, zTurn z = (-z2, z1 - 1);
    lv, te, c_e from oc.frame(u) (shift, offset, constant), aq = (n_q, -d_q).
    W0 (eps=-1): Psi(H_0)=0, Psi(H_1)=1, Psi(H_j)>=1 (j>=1), Psi(H_j) nondecreasing in j.
    W1 (eps=+1): w(H_j) = (d+1-x, n-1-y), Psi(w H_0)=Psi(H_last)=0, Psi(w H_1)=1, Psi(w H_j)>=1 (j>=1), nondecreasing in j."""
import sys
sys.path.insert(0, 'scripts'); sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w3/scripts')
from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import open_inputs_check as oc
import exact_quotient as eq
import w1_pinned_edges as PE
from w1_arc_prescription import F as Frame

def harmonic(x):
    x1, x2 = x
    return (x1 * x1 + 2 * x1 * x2 - x2 * x2 - 2 * x2 - ((x1 + x2) % 2)) // 4

def job(u):
    cw = PE.conj_of(u)
    fu = oc.frame(list(u))
    eps, n, d, nq, dq, N, D = fu['eps'], fu['n'], fu['d'], fu['nq'], fu['dq'], fu['N'], fu['D']
    ec = oc.frame(list(cw))['eps']
    lv, te, ce = fu['shift'], fu['offset'], fu['constant']
    out = {'u': u, 'eps': eps, 'eps_c': ec}
    # (a) pins at eta = eps(u)
    pins = PE.check(cw, eps)
    out['pins'] = {k: v['admissible'] for k, v in pins.items()}
    # (b) Psi on the H trace
    G, _ = pl.standard(tuple(cw))
    def FqW(z):
        return G((-z[1], z[0] - 1)) + harmonic(z)
    def Psi(z):
        zl = (z[0] - lv[0], z[1] - lv[1])
        A = FqW(zl)
        C = FqW((zl[0] - te[0], zl[1] - te[1])) + (nq * zl[0] - dq * zl[1]) + ce
        return C - A
    fr = Frame(n, d)
    H = {}
    ok = True
    for x in range(1, d + 1):
        ys = [y for y in range(-3 * fr.L - 3 * fr.T - 5, 3 * fr.L + 3 * fr.T + 5) if fr.freeH((x, y))]
        if len(ys) != 1:
            ok = False; break
        H[x] = (x, ys[0])
    out['H_one_per_abscissa'] = ok
    if not ok:
        return out
    W = (1 + eps) // 2
    if W == 0:
        seq = [Psi(H[j + 1]) for j in range(d)]
        out['exc'] = ('H0', Psi(H[1]), 'H1', Psi(H[2]) if d >= 2 else None)
    else:
        seq = [Psi((d + 1 - H[j + 1][0], n - 1 - H[j + 1][1])) for j in range(d)]
        out['exc'] = ('Hlast', seq[0], 'H_{d-2}', seq[1] if d >= 2 else None)
    out['seq'] = seq
    out['exc_ok'] = (seq[0] == 0 and seq[1] == 1)
    out['ge1_others'] = all(v >= 1 for v in seq[1:])
    out['nondecr'] = all(seq[j] <= seq[j + 1] for j in range(d - 1))
    return out

if __name__ == '__main__':
    ws = list(eq.words(4))
    tot = Counter(); bad = []
    with Pool(8) as pool:
        for out in pool.imap_unordered(job, ws):
            if 'pins' in out:
                for name, adm in out['pins'].items():
                    tot[('pin', out['eps'], out['eps_c'], name, 'adm' if adm else 'NOT')] += 1
            tot[('H one per abscissa', out['H_one_per_abscissa'])] += 1
            if out['H_one_per_abscissa']:
                tot[('exceptional values ok (W%d)' % ((1 + out['eps']) // 2), out['exc_ok'])] += 1
                tot[('Psi>=1 at all other H', out['ge1_others'])] += 1
                tot[('Psi nondecreasing in j', out['nondecr'])] += 1
                if not (out['exc_ok'] and out['ge1_others'] and out['nondecr']):
                    bad.append(out)
    for k in sorted(tot, key=str):
        print(k, tot[k])
    print('failing words (Psi checks):', len(bad))
    for b in bad[:5]:
        print({k: b[k] for k in ('u', 'eps', 'exc', 'seq') if k in b})
