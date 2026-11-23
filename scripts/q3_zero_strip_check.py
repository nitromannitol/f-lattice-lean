"""Task 59 paragraph 8 (numerical): the zero strip of the quarter-turned earlier field (StrongEstimates.zeroStripInterval):
f(x) = G(Zx) + h0(x) vanishes for 1 - D <= t_p(x) <= N + 2D - 1, t_p(x) = N x1 - D x2, on the window box of the word.
And the H-root arguments: for the web values t in {1..N+D-1} u {0, N+D} (even) u {N..D} u {D+1} (odd), t and t+1 lie in the strip;
t_p(x + eps U_q) = t_p(x) + 1 for U_q = (d_q, n_q). Words of length <= 4 (non-cube, conjugate nonempty).
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    if all(x == 3 for x in w):
        return {}
    u = list(pl.swap(pl.odd_birth_prefix(w)))
    if not u:
        return {"conjugate empty, skipped": 1}
    G, _ = pl.standard(tuple(u))
    h0 = pl.h0
    fr = oc.frame(w)
    N, D, nq, dq, eps = fr["N"], fr["D"], fr["nq"], fr["dq"], fr["eps"]
    f = lambda x: G((-x[1], x[0] - 1)) + h0(*x)
    tp = lambda x: N * x[0] - D * x[1]
    out = defaultdict(int)
    x0, x1, y0, y1 = oc.window(fr)
    for zy in range(y0, y1 + 1):
        for zx in range(x0, x1 + 1):
            x = (zx, zy)
            t = tp(x)
            if 1 - D <= t <= N + 2 * D - 1:
                out[("zero strip: f(x) = 0", f(x) == 0)] += 1
            xu = (x[0] + eps * dq, x[1] + eps * nq)
            out[("tp(x + eps Uq) = tp(x) + 1", tp(xu) == t + 1)] += 1
            # H-web values: arguments x and x + eps Uq lie in the strip when t is a web value
            web = (1 <= t <= N + D - 1) or t == 0 or t == N + D or (N <= t <= D) or t == D + 1
            if web:
                ok = (1 - D <= t <= N + 2 * D - 1) and (1 - D <= t + 1 <= N + 2 * D - 1)
                out[("web value: t, t+1 in strip", ok)] += 1
                if ok:
                    out[("web value: a = f(x+eps Uq) - f(x) = 0", f(xu) - f(x) == 0)] += 1
    return out


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    with Pool(12) as pool:
        for out in pool.imap_unordered(run, ws):
            for k, v in out.items():
                tot[k] += v
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
