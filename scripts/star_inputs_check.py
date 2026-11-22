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
    x0, x1, y0, y1 = bbox(frm)
    out_pts, out_bad, out_vals = 0, 0, set()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            even = (x + y) % 2 == 0
            ins = [(x - 1, y), (x + 1, y)] if even else [(x, y - 1), (x, y + 1)]
            for q in ins:
                if not frm.inE(q):
                    out_pts += 1
                    v = Dp(q)
                    out_vals.add(v)
                    if not (0 <= v <= 2):
                        out_bad += 1
    return tuple(w), out_pts, out_bad, out_vals

if __name__ == "__main__":
    tot = dict(outside_inputs=0, outside_bad=0)
    vals = set()
    with Pool(12) as pool:
        for w, op, ob, vs in pool.imap_unordered(run, list(words(4))):
            tot["outside_inputs"] += op; tot["outside_bad"] += ob; vals |= vs
    print("TOTAL", tot, "values:", sorted(vals), flush=True)
