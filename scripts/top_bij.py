from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d = frm.n, frm.d
    V = (n - d, n + d)
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
    img = {(p[0] - V[0], p[1] - V[1]) for p in pure_t}
    return tuple(w), len(pure_t), len(pure_b), len(img & pure_b), img == pure_b

if __name__ == "__main__":
    tot = dict(top=0, bot=0, inter=0, equal_words=0, words=0)
    bad = []
    with Pool(12) as pool:
        for w, nt, nb, inter, eq in pool.imap_unordered(run, list(words(4))):
            tot["top"] += nt; tot["bot"] += nb; tot["inter"] += inter; tot["equal_words"] += eq; tot["words"] += 1
            if not eq: bad.append((len(w), w, nt, nb, inter))
    print("TOTAL", tot, flush=True)
    for b in sorted(bad)[:4]:
        print("NOT_EQUAL", b, flush=True)
