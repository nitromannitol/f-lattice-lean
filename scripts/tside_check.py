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
    Dp = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    T, L, n, d = frm.T, frm.L, frm.n, frm.d
    x0, x1, y0, y1 = bbox(frm)
    out = {}
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            even = (x + y) % 2 == 0
            tl, tu = (2 - T, L - 2) if even else (n - T, d)
            t = frm.t(p)
            if t in (tl, tu):
                key = ("even" if even else "odd", "lo" if t == tl else "hi")
                out.setdefault(key, {}).setdefault(Dp(p), 0)
                out[key][Dp(p)] += 1
    return tuple(w), out

if __name__ == "__main__":
    tot = {}
    with Pool(12) as pool:
        for w, out in pool.imap_unordered(run, list(words(4))):
            for k, dd in out.items():
                for v, c in dd.items():
                    tot.setdefault(k, {}).setdefault(v, 0)
                    tot[k][v] += c
    for k in sorted(tot):
        print(k, tot[k], flush=True)
