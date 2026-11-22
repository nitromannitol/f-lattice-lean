from multiprocessing import Pool
import permit_local as pl, restricted_escape as re_
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    T, L, n, d = frm.T, frm.L, frm.n, frm.d
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    F, _ = pl.standard(tuple(w))
    Dp = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    x0, x1, y0, y1 = bbox(frm)
    st = dict(bnd=0, on_t_side=0, on_s_side=0, on_neither=0, t_side_pts=0, s_side_pts=0, tside_D0=0, tside_D2=0, sside_in=0, sside_n=0)
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            outside = any(not frm.inE((x + dx, y + dy)) for dx, dy in ((1,0),(-1,0),(0,1),(0,-1)))
            t, s = frm.t(p), frm.sg(p)
            even = (x + y) % 2 == 0
            if even:
                tl, tu, sl, su = 2 - T, L - 2, 0, T + 2 * n
            else:
                tl, tu, sl, su = n - T, d, 2 - d + n, T + L - 2
            ont = t in (tl, tu)
            ons = s in (sl, su)
            if t in (tl, tu):
                st["t_side_pts"] += 1
                if Dp(p) == 0: st["tside_D0"] += 1
                if Dp(p) == 2: st["tside_D2"] += 1
            if s in (sl, su):
                st["s_side_pts"] += 1
            if not outside:
                continue
            st["bnd"] += 1
            if ont: st["on_t_side"] += 1
            elif ons: st["on_s_side"] += 1
            else: st["on_neither"] += 1
    return tuple(w), st

if __name__ == "__main__":
    tot = {}
    with Pool(12) as pool:
        for w, st in pool.imap_unordered(run, list(words(4))):
            for k, v in st.items(): tot[k] = tot.get(k, 0) + v
    print("TOTAL", tot, flush=True)
