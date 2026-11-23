"""Task 60: the native V path of the odd parent (words <= 4), numerical checks before Lean.

(1) floors: for 1 <= l < D, floor((d-n) l / d) == floor((D-N) l / D).
(2) the odd native vertices v_l = (-b'_l, 2l-1-b'_l), b'_l = floor((D-N) l / D), 1 <= l <= D-1, lie in the box
    N-D+1 <= x1 <= 0, 0 <= x2 <= D+N-1, and the box has t_p in [r-B, 0], r = D+N, B = D^2+2DN-N^2 (t_p = N x1 - D x2).
    The endpoint V_p + I = (N-D+1, D+N-1) has t_p = r - B.
(3) a(x) = f(x + eps Uq) - f(x) in {0,1} at the box points with t_p in [r-B, 0]; f = quarterTurn(G), G = standard(conjWord).
(4) a(x + j V_p) = a(x) + j for V_p = (N-D, N+D) (where defined on the window).
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
    n, d = fr["n"], fr["d"]
    r = D + N
    B = D * D + 2 * D * N - N * N
    f = lambda x: G((-x[1], x[0] - 1)) + h0(*x)
    tp = lambda x: N * x[0] - D * x[1]
    out = defaultdict(int)
    # (1) floors
    for l in range(1, D):
        out[("(1) floor(child) == floor(parent), 1<=l<D", (d - n) * l // d == (D - N) * l // D)] += 1
    # (2) odd vertices and box
    for l in range(1, D):
        bp = (D - N) * l // D
        v = (-bp, 2 * l - 1 - bp)
        out[("(2) odd vertex in box", (N - D + 1 <= v[0] <= 0) and (0 <= v[1] <= D + N - 1))] += 1
        out[("(2) odd vertex t_p in [r-B,0]", r - B <= tp(v) <= 0)] += 1
    # box claim over the full box
    ok_box = True
    for x1 in range(N - D + 1, 1):
        for x2 in range(0, D + N):
            if not (r - B <= tp((x1, x2)) <= 0):
                ok_box = False
    out[("(2) box points t_p in [r-B, 0]", ok_box)] += 1
    out[("(2) V_p + I has t_p = r - B", tp((N - D + 1, D + N - 1)) == r - B)] += 1
    # (3) a in {0,1} at box points with t_p in [r-B, 0]; (4) translation by V_p
    Vp = (N - D, N + D)
    a = lambda x: f((x[0] + eps * dq, x[1] + eps * nq)) - f(x)
    for x1 in range(N - D + 1, 1):
        for x2 in range(0, D + N):
            x = (x1, x2)
            if r - B <= tp(x) <= 0:
                out[("(3) a(x) in {0,1} on box", a(x) in (0, 1))] += 1
            for j in (1, -1):
                y = (x[0] + j * Vp[0], x[1] + j * Vp[1])
                if (N * y[0] - D * y[1]) is not None:
                    out[("(4) a(x + j Vp) = a(x) + j (j=%+d)" % j, a(y) == a(x) + j)] += 1
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
