"""Task 35 (2): pure bottom / pure top arcs against the packet strips, all 116 words.
zero strip: 1-d <= t <= n+2d-1 (t = n x - d y); h0 strip: 1-2d <= s <= 2L-1 (s = L x + (d-n) y).
Also: pure top = pure bottom + V ? and the sigma-shift's t and s."""
from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    n, d, L, T = frm.n, frm.d, frm.L, frm.T
    x0, x1, y0, y1 = bbox(frm)
    bottom, top = set(), set()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            o = {nm for nm, dd in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                 if not frm.inE((x + dd[0], y + dd[1]))}
            if o == {"S"}:
                bottom.add(p)
            if o == {"N"}:
                top.add(p)
    st = dict(bot=len(bottom), bot_t_in=0, bot_shift_t_same=0, top=len(top), top_s_in_h0=0, top_shift_s_in_h0=0,
              top_eq_bottom_plus_V=0, bottom_in_V_top=0)
    for p in bottom:
        t = frm.t(p)
        if 1 - d <= t <= n + 2 * d - 1:
            st["bot_t_in"] += 1
        q = (p[0] + sig[0], p[1] + sig[1])
        if frm.t(q) == t:
            st["bot_shift_t_same"] += 1
    V = (n - d, n + d)
    for p in top:
        s = frm.sg(p)
        if 1 - 2 * d <= s <= 2 * L - 1:
            st["top_s_in_h0"] += 1
        q = (p[0] + sig[0], p[1] + sig[1])
        sq = frm.sg(q)
        if 1 - 2 * d <= sq <= 2 * L - 1:
            st["top_shift_s_in_h0"] += 1
    bpV = {(p[0] + V[0], p[1] + V[1]) for p in bottom}
    st["top_eq_bottom_plus_V"] = int(bpV == top)
    return tuple(w), st

if __name__ == "__main__":
    tot = {}
    with Pool(12) as pool:
        for w, st in pool.imap_unordered(run, list(words(4))):
            for k, v in st.items():
                tot[k] = tot.get(k, 0) + v
    print("TOTAL", tot, flush=True)
