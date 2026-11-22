"""Task 34 (3): is the right boundary the left boundary shifted by U (kernel period, D+ equal)? Split by pattern."""
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
    outs = {}
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            o = frozenset(nm for nm, d in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                          if not frm.inE((x + d[0], y + d[1])))
            if o:
                outs[p] = o
    U = (frm.d, frm.n)
    res = {}
    for p, o in outs.items():
        if "E" not in o:
            continue
        q = (p[0] - U[0], p[1] - U[1])
        key = ("".join(sorted(o)), "".join(sorted(outs.get(q, set()))))
        ok = (q in outs) and ("W" in outs[q]) and Dp(q) == Dp(p)
        res[key] = res.get(key, [0, 0])
        res[key][0 if ok else 1] += 1
    return tuple(w), res

if __name__ == "__main__":
    tot = {}
    with Pool(12) as pool:
        for w, res in pool.imap_unordered(run, list(words(4))):
            for k, (a, b) in res.items():
                t = tot.setdefault(k, [0, 0])
                t[0] += a; t[1] += b
    for k, v in sorted(tot.items()):
        print("E-pattern", k[0], "-> shifted pattern", k[1], "ok", v[0], "fail", v[1], flush=True)
