from multiprocessing import Pool
from collections import Counter
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d, T, L = frm.n, frm.d, frm.T, frm.L
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    U, V, I = (d, n), (n - d, n + d), (1, -1)
    c = (U[0] + V[0] + I[0], U[1] + V[1] + I[1])
    x0, x1, y0, y1 = bbox(frm)
    E = frm.inE
    lo_s, hi_s = 3 - d, n + 2 * d - 1
    def st0(q): return lo_s <= frm.t(q) <= hi_s
    def st2(q): return lo_s <= frm.t(q) + T <= hi_s
    def win(q):
        even = (q[0] + q[1]) % 2 == 0
        lo, hi = (2 - T, L - 2) if even else (n - T, d)
        return lo <= frm.t(q) <= hi
    def side(p, u):
        return ("W" if u[0] < p[0] else "E") if u[1] == p[1] else ("S" if u[1] < p[1] else "N")
    halo_tot = halo_cov = 0
    vtot = vcov = 0
    vleft = Counter()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not E(p): continue
            even = (x + y) % 2 == 0
            r = (c[0] - sig[0] - p[0], c[1] - sig[1] - p[1])
            # V-arc points: outward W or E
            isV = (not E((x - 1, y))) or (not E((x + 1, y)))
            if isV:
                vtot += 1
                if st0(p) or st2(p) or st0(r) or st2(r):
                    vcov += 1
                else:
                    vleft[("even" if even else "odd")] += 1
            ins = [(x - 1, y), (x + 1, y)] if even else [(x, y - 1), (x, y + 1)]
            for u in ins:
                if E(u): continue
                halo_tot += 1
                ru = (c[0] - sig[0] - u[0], c[1] - sig[1] - u[1])
                ok = win(u) or win(ru) or st0(u) or st2(u) or st0(ru) or st2(ru)
                halo_cov += ok
    return tuple(w), halo_tot, halo_cov, vtot, vcov, vleft

if __name__ == "__main__":
    tot = dict(halo=0, halo_cov=0, varc=0, varc_cov_strip_only=0)
    vl = Counter()
    with Pool(12) as pool:
        for w, ht, hc, vt, vc, vlf in pool.imap_unordered(run, list(words(4))):
            tot["halo"] += ht; tot["halo_cov"] += hc; tot["varc"] += vt; tot["varc_cov_strip_only"] += vc
            vl.update(vlf)
    print("TOTAL", tot, "V-arc uncovered by strips:", dict(vl), flush=True)
