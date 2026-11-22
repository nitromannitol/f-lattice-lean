from multiprocessing import Pool
from collections import Counter
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
    def inc(z):
        if (z[0] + z[1]) % 2 == 0:
            return [(z[0] - 1, z[1]), (z[0] + 1, z[1])]
        return [(z[0], z[1] - 1), (z[0], z[1] + 1)]
    def lap(z):
        a, b = inc(z)
        return F(a) + F(b) - 2 * F(z)
    x0, x1, y0, y1 = bbox(frm)
    cnt = Counter()
    for x in range(x0 - 2, x1 + 3):
        for y in range(y0 - 2, y1 + 3):
            c = (x, y)
            lc = lap(c)
            lcs = lap((c[0] + sig[0], c[1] + sig[1]))
            a, b = inc(c)
            dc = Dp(c)
            e = (Dp(a) - dc, Dp(b) - dc)
            cfg = ("B" if lc == -1 else "W", lcs, dc, tuple(sorted(e)), "in-range" if all(0 <= Dp(q) <= 2 for q in (a, b, c)) else "out")
            cnt[cfg] += 1
    return tuple(w), cnt

if __name__ == "__main__":
    tot = Counter()
    with Pool(12) as pool:
        for w, c in pool.imap_unordered(run, list(words(4))):
            tot.update(c)
    for k, v in sorted(tot.items(), key=lambda kv: str(kv[0])):
        print(k, v)
