"""(c) hwin with the CONJUGATE field: F = G = standardField(conjWord u) on the conjugate child frame (D-N, D+N) (the policy field).
Same statement as w1_window_check.py: for v0 with openRect v0 and G v0 = capMin(0) = 0 and every i in the closed polygon of the
conjugate child: capMin(i.2 - v0.2) <= G i."""
import sys
sys.path.insert(0, 'scripts'); sys.path.insert(0, 'scripts')
from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import exact_quotient as eq
import w1_pinned_edges as PE
from w1_arc_prescription import F as Frame, even

def capMin(k):
    return -(k * (k - 1) // 2)

def job(u):
    cw = PE.conj_of(u)
    import open_inputs_check as oc
    fc = oc.frame(list(cw))
    nc, dc = fc['n'], fc['d']
    G, _ = pl.standard(tuple(cw))
    fr = Frame(nc, dc)
    L, T = fr.L, fr.T
    def openRect(z):
        t, s = fr.t(z), fr.s(z)
        if even(z):
            return (L - 2 - T < t < 2) and (2 * nc < s < T)
        return (dc - T < t < nc) and (L - 2 < s < T + 2 - dc + nc)
    E = [(x, y) for x in range(-2 * dc - 2, 2 * dc + 3) for y in range(-2 * L - 2, 2 * L + 3) if fr.cp((x, y))]
    Ev = {i: G(i) for i in E}
    starts = []
    for x in range(-3 * dc, 3 * dc + 1):
        for y in range(-3 * L, 3 * L + 1):
            v0 = (x, y)
            if (not even(v0)) and openRect(v0) and G(v0) == capMin(0):
                starts.append(v0)
    bad = None
    for v0 in starts:
        for i in E:
            if capMin(i[1] - v0[1]) > Ev[i]:
                bad = (v0, i, capMin(i[1] - v0[1]), Ev[i]); break
        if bad: break
    return u, nc, dc, len(E), len(starts), bad

if __name__ == '__main__':
    tot = Counter(); samples = []
    with Pool(8) as pool:
        for u, nc, dc, nE, nS, bad in pool.imap_unordered(job, list(eq.words(4))):
            tot[('window holds (conjugate field)', bad is None)] += 1
            tot[('starts>0', nS > 0)] += 1
            if bad and len(samples) < 4: samples.append((u, (nc, dc), bad))
    for k in sorted(tot, key=str): print(k, tot[k])
    for s_ in samples: print(s_)
