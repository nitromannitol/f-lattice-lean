from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d = frm.n, frm.d
    V = (n - d, n + d); U = (d, n)
    x0, x1, y0, y1 = bbox(frm)
    pure_b, pure_t = set(), set()
    tmin = None; tmax = None
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            o = {nm for nm, dd in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                 if not frm.inE((x + dd[0], y + dd[1]))}
            if o == {"S"}:
                pure_b.add(p)
                t = frm.t(p)
                tmin = t if tmin is None else min(tmin, t)
                tmax = t if tmax is None else max(tmax, t)
            if o == {"N"}: pure_t.add(p)
    # for each pure top p, does some k with p - V - k*U lie in pure_b ?
    ok = 0
    for p in pure_t:
        base = (p[0] - V[0], p[1] - V[1])
        found = False
        for k in range(-200, 201):
            if (base[0] - k * U[0], base[1] - k * U[1]) in pure_b:
                found = True
                break
        ok += found
    return tuple(w), len(pure_t), ok, tmin, tmax, 3 - d, n + 2 * d - 1

if __name__ == "__main__":
    tot = dict(top=0, corr=0, bad_words=0)
    tlow_ok = 0
    with Pool(12) as pool:
        for w, nt, ok, tmin, tmax, lo, hi in pool.imap_unordered(run, list(words(4))):
            tot["top"] += nt; tot["corr"] += ok
            if ok != nt: tot["bad_words"] += 1
            if tmin is not None and lo <= tmin and tmax <= hi: tlow_ok += 1
    print("TOTAL", tot, "words with t(pure bottom) inside [3-d, n+2d-1]:", tlow_ok, "of 116", flush=True)
