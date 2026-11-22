from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def trange(frm, even):
    T, L, n, d = frm.T, frm.L, frm.n, frm.d
    return (2 - T, L - 2) if even else (n - T, d)

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d, T, L = frm.n, frm.d, frm.T, frm.L
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    U, V, I = (d, n), (n - d, n + d), (1, -1)
    c = (U[0] + V[0] + I[0], U[1] + V[1] + I[1])
    x0, x1, y0, y1 = bbox(frm)
    tot = A = B = AB_none = 0
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            even = (x + y) % 2 == 0
            ins = [(x - 1, y), (x + 1, y)] if even else [(x, y - 1), (x, y + 1)]
            for u in ins:
                if frm.inE(u):
                    continue
                tot += 1
                ue = (u[0] + u[1]) % 2 == 0
                lo, hi = trange(frm, ue)
                okA = lo <= frm.t(u) <= hi
                r = (c[0] - sig[0] - u[0], c[1] - sig[1] - u[1])
                re = (r[0] + r[1]) % 2 == 0
                lo2, hi2 = trange(frm, re)
                okB = lo2 <= frm.t(r) <= hi2
                A += okA
                B += (not okA) and okB
                AB_none += (not okA) and (not okB)
    return tuple(w), tot, A, B, AB_none

if __name__ == "__main__":
    tot = dict(outside=0, kernel_ok=0, reflect_ok=0, neither=0)
    with Pool(12) as pool:
        for w, t, a, b, nn in pool.imap_unordered(run, list(words(4))):
            tot["outside"] += t; tot["kernel_ok"] += a; tot["reflect_ok"] += b; tot["neither"] += nn
    print("TOTAL", tot, flush=True)
