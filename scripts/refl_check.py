from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    frm = pl.Frame(w)
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    n, d, T, L = frm.n, frm.d, frm.T, frm.L
    U, V, I = (d, n), (n - d, n + d), (1, -1)
    c = (U[0] + V[0] + I[0], U[1] + V[1] + I[1])
    rho = lambda x: (c[0] - sig[0] - x[0], c[1] - sig[1] - x[1])
    t = frm.t
    Dp = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    x0, x1, y0, y1 = bbox(frm)
    # reflection constant check on a box
    ks = set()
    for x in range(x0 - 2, x1 + 3):
        for y in range(y0 - 2, y1 + 3):
            z = (x, y)
            ks.add(F((c[0] - x, c[1] - y)) - F(z) + t(z))
    refl_const = len(ks) == 1
    E_pts = inE = in_img = id_ok = 0
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            E_pts += 1
            r = rho(p)
            if frm.inE(r):
                in_img += 1
            if Dp(r) == 2 - Dp(p):
                id_ok += 1
    return tuple(w), refl_const, E_pts, in_img, id_ok

if __name__ == "__main__":
    tot = dict(words=0, refl_const=0, E_pts=0, rho_in_E=0, identity_ok=0)
    with Pool(12) as pool:
        for w, rc, ep, ri, io in pool.imap_unordered(run, list(words(4))):
            tot["words"] += 1; tot["refl_const"] += rc; tot["E_pts"] += ep
            tot["rho_in_E"] += ri; tot["identity_ok"] += io
    print("TOTAL", tot, flush=True)
