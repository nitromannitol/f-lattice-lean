"""(c) The global window of the cap (task 118): hwin of FreeRows.free_row_empty, for F = standardField(u) on the child frame of u.
For every site v0 in a box with openRect v0 and F v0 = parabola v0.2 v0 (= capMin 0 = 0), and every i in the closed polygon E:
  capMin(i.2 - v0.2) <= F i, with capMin k = -(k(k-1)/2) (QuadraticCap.lean). openRect is the PROVISIONAL reading (Q3Exit.lean)."""
import sys
sys.path.insert(0, 'scripts'); sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w3/scripts')
from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import open_inputs_check as oc
import exact_quotient as eq
from w1_arc_prescription import F as Frame, even

def capMin(k):
    return -(k * (k - 1) // 2)

def job(u):
    fu = oc.frame(list(u))
    n, d, eps = fu['n'], fu['d'], fu['eps']
    Fu, _ = pl.standard(tuple(u))
    fr = Frame(n, d)
    L, T = fr.L, fr.T
    def openRect(z):
        t, s = fr.t(z), fr.s(z)
        if even(z):
            return (L - 2 - T < t < 2) and (2 * n < s < T)
        return (d - T < t < n) and (L - 2 < s < T + 2 - d + n)
    E = [(x, y) for x in range(-2 * d - 2, 2 * d + 3) for y in range(-2 * L - 2, 2 * L + 3) if fr.cp((x, y))]
    Ev = {i: Fu(i) for i in E}
    starts = []
    for x in range(-3 * d, 3 * d + 1):
        for y in range(-3 * L, 3 * L + 1):
            v0 = (x, y)
            if openRect(v0) and Fu(v0) == capMin(0):
                starts.append(v0)
    bad = []
    for v0 in starts:
        for i in E:
            if capMin(i[1] - v0[1]) > Ev[i]:
                bad.append((v0, i, capMin(i[1] - v0[1]), Ev[i]))
                break
        if bad:
            break
    return u, n, d, len(E), len(starts), bad[:1]

if __name__ == '__main__':
    tot = Counter(); samples = []
    with Pool(8) as pool:
        for u, n, d, nE, nS, bad in pool.imap_unordered(job, list(eq.words(4))):
            tot[('window holds', not bad)] += 1
            tot[('starts>0', nS > 0)] += 1
            if bad and len(samples) < 4: samples.append((u, n, d, bad))
    for k in sorted(tot, key=str): print(k, tot[k])
    for s_ in samples: print(s_)
