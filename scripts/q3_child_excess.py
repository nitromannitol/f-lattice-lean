"""Task 59 step 1: excess of the child's free H/V sites outside the parent web (exact transform), modular test.

For a range [lo, hi] and modulus M, excess = min over k of the distance from (v - kM) to [lo, hi] (0 inside).
Reports, per parity label and per word length, the distribution of excesses. Words of length <= 4.
"""
from multiprocessing import Pool
from collections import defaultdict
import open_inputs_check as oc
from exact_quotient import words


def excess(v, lo, hi, M):
    best = None
    for k in range(-3, 4):
        u = v - k * M
        e = max(lo - u, 0, u - hi)
        best = e if best is None else min(best, e)
    return best


def run(w):
    w = list(w)
    fr = oc.frame(w)
    N, D, n, d, T, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"], fr["eps"]
    L = n + d
    Lp, Tp = D + N, D * D + 2 * D * N - N * N
    C = D * L + N * (d - n)
    tgr = lambda z: n * z[0] - d * z[1]
    sgr = lambda z: L * z[0] + (d - n) * z[1]
    out = defaultdict(int)
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    Hspec = set(range(2, L - 1, 2)) | set(range(n, d + 1, 2))
    Vspec = set(range(0, 2 * n + 1, 2)) | set(range(2 - d + n, L - 1, 2))
    Hb = [z for z in reps if not inE((z[0], z[1] - 1)) and tgr(z) in Hspec]
    Vb = [z for z in reps if not inE((z[0] - 1, z[1])) and sgr(z) in Vspec]
    for z in Hb:
        tp = (C * tgr(z) + eps * sgr(z)) // T
        ev = oc.even_site(z)
        lo, hi = (1, Lp - 1) if ev else (N, D)
        out[("H", "even" if ev else "odd", excess(tp, lo, hi, Tp))] += 1
    for z in Vb:
        sp = (C * sgr(z) + 2 * eps * tgr(z)) // T
        ev = oc.even_site(z)
        lo, hi = (0, 2 * N) if ev else (2 - D + N, Lp - 2)
        out[("V", "even" if ev else "odd", excess(sp, lo, hi, 2 * Tp))] += 1
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
