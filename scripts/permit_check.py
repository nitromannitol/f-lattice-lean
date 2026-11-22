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
    lap = lambda z: (F((z[0] - 1, z[1])) if (z[0] + z[1]) % 2 == 0 else F((z[0], z[1] - 1))) + 0  # placeholder
    def inc(z):
        if (z[0] + z[1]) % 2 == 0:
            return [(z[0] - 1, z[1]), (z[0] + 1, z[1])]
        return [(z[0], z[1] - 1), (z[0], z[1] + 1)]
    def L(z):
        a, b = inc(z)
        return F(a) + F(b) - 2 * F(z)
    x0, x1, y0, y1 = bbox(frm)
    black = bad_black = white = bad_white = 0
    for x in range(x0 - 3, x1 + 4):
        for y in range(y0 - 3, y1 + 4):
            c = (x, y)
            l = L(c)
            a, b = inc(c)
            if l == -1:
                black += 1
                if not (Dp(a) - Dp(c) <= 0 and Dp(b) - Dp(c) <= 0):
                    bad_black += 1
            elif l == 0:
                white += 1
                if not (Dp(a) - Dp(c) <= 0 or Dp(b) - Dp(c) <= 0):
                    bad_white += 1
    return tuple(w), black, bad_black, white, bad_white

if __name__ == "__main__":
    tot = dict(black=0, bad_black=0, white=0, bad_white=0)
    with Pool(12) as pool:
        for w, b, bb, wh, bw in pool.imap_unordered(run, list(words(4))):
            tot["black"] += b; tot["bad_black"] += bb; tot["white"] += wh; tot["bad_white"] += bw
    print("TOTAL", tot, flush=True)
