from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox
from top_bij import *

def run2(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d = frm.n, frm.d
    V = (n - d, n + d); U = (d, n)
    x0, x1, y0, y1 = bbox(frm)
    pure_b, pure_t = set(), set()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            o = {nm for nm, dd in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                 if not frm.inE((x + dd[0], y + dd[1]))}
            if o == {"S"}: pure_b.add(p)
            if o == {"N"}: pure_t.add(p)
    found = []
    for k in range(-60, 61):
        img = {(p[0] - V[0] - k * U[0], p[1] - V[1] - k * U[1]) for p in pure_t}
        if img == pure_b:
            found.append(k)
    return tuple(w), found

if __name__ == "__main__":
    res = []
    with Pool(12) as pool:
        for w, f in pool.imap_unordered(run2, list(words(4))):
            res.append((len(w), w, f))
    print("words with a k:", sum(1 for r in res if r[2]), "of", len(res), flush=True)
    for r in sorted(res)[:5]:
        print("WORD", r, flush=True)
