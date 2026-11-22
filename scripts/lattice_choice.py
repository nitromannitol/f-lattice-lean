from multiprocessing import Pool
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
    rho = lambda x: (c[0] - sig[0] - x[0], c[1] - sig[1] - x[1])
    x0, x1, y0, y1 = bbox(frm)
    bad = 0; cnt = 0; jdist = [0, 0]
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            cnt += 1
            r = rho(p)
            tr, sr = frm.t(r), frm.sg(r)
            even = (p[0] + p[1]) % 2 == 0
            if even:
                tlo, thi, slo, shi = 2 - T, L - 2, 0, T + 2 * n
            else:
                tlo, thi, slo, shi = n - T, d, 2 - d + n, T + L - 2
            ok = False
            for j in (0, 1):
                tj = tr - j * T
                if tlo <= tj <= thi:
                    # choose k so that s + kT in [slo, slo+T-1]
                    k = -((sr - slo) // T)
                    sk = sr + k * T
                    if slo <= sk <= shi:
                        y2 = (r[0] + k * U[0] + j * V[0], r[1] + k * U[1] + j * V[1])
                        if frm.inE(y2):
                            ok = True
                            jdist[j] += 1
                            break
            if not ok:
                bad += 1
    return tuple(w), cnt, bad, jdist

if __name__ == "__main__":
    tot = dict(points=0, no_rep=0, j0=0, j1=0)
    with Pool(12) as pool:
        for w, cnt, bad, jd in pool.imap_unordered(run, list(words(4))):
            tot["points"] += cnt; tot["no_rep"] += bad; tot["j0"] += jd[0]; tot["j1"] += jd[1]
    print("TOTAL", tot, flush=True)
