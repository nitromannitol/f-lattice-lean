"""Task 60 (lead): the l = D block vertex uses the CHILD floor, b_c = floor((d-n) D / d) = D - N + floor(eps/d).
Block vertex at l: v_l = (-b, 2l - 1 - b) with b = floor((d-n) l / d) (child), for every 1 <= l <= D.
W = 0 (eps = -1): the block is v_1..v_D; every v_l is a child left V vertex (left boundary of E, parity spectrum).
W = 1 (eps = +1): the block is v_1..v_{D-1} and V_p + I = (N-D+1, D+N-1) replaces v_D (child floor D-N, v_D = (N-D, D+N-1)).
Also: exceptional V_p + I is not a child left V vertex when W = 1 (s = 2n + 2 > 2n on the even branch).
"""
from multiprocessing import Pool
from collections import defaultdict
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    fr = oc.frame(w)
    N, D, n, d, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["eps"]
    W = (1 + eps) // 2
    L = n + d
    inE = lambda z: oc.in_polygon(z, fr)
    sg = lambda z: L * z[0] + (d - n) * z[1]
    def left_bdry(z):
        return inE(z) and not inE((z[0] - 1, z[1]))
    def spec(z):
        if oc.even_site(z):
            return 0 <= sg(z) <= 2 * n
        return 2 - d + n <= sg(z) <= L - 2
    out = defaultdict(int)
    key = "W=%d" % W
    for l in range(1, D + 1):
        b = (d - n) * l // d            # child floor
        v = (-b, 2 * l - 1 - b)
        if l < D:
            out[(key, "block l<D: child left V vertex", left_bdry(v) and spec(v))] += 1
        elif eps == -1:
            out[(key, "block l=D (W=0, child floor): child left V vertex", left_bdry(v) and spec(v))] += 1
            out[(key, "block l=D (W=0): v == (N-D+1, D+N)", v == (N - D + 1, D + N))] += 1
            out[(key, "block l=D (W=0): s == L-2", sg(v) == L - 2)] += 1
        else:
            out[(key, "l=D (W=1): child floor equals D-N", b == D - N)] += 1
    if eps == 1:
        vp = (N - D + 1, D + N - 1)
        out[(key, "V_p+I (W=1): NOT a left V vertex", not (left_bdry(vp) and spec(vp)))] += 1
        out[(key, "V_p+I (W=1): s == 2n+2", sg(vp) == 2 * n + 2)] += 1
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
