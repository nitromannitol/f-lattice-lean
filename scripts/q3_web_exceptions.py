"""Task 59 step 1: the exact web of the odd parent (words <= 4), with its exceptions.

Child free H/V sites (oc.frame conventions) in parent coordinates tp = N x1 - D x2, sp = (D+N) x1 + (D-N) x2, Lp = D+N.
Regular web: even-site H: tp in [1, Lp-1]; odd-site H: tp in [N, D]; odd-site V: sp in [2-D+N, Lp-2];
even-site V: sp in [0, 2N].
Exceptions (predicted, all checked exactly):
  E1 even H with r = 2Nl mod Lp = 0 (site (2l-b, b), l = (x1+x2)/2): tp = Lp if eps = +1, tp = 0 if eps = -1.
  E2 odd H at H_{d-1} = (d, n-1) (t = d): tp = D + eps  (outside [N, D] iff eps = +1, then tp = D+1).
  E3 odd V with (D-N) l = 0 mod D (site (-b, 2l-1-b), l = (x2-x1+1)/2): sp = N-D if eps = +1 (f = 0), sp = Lp if eps = -1 (f = D).
  E4 even V at V_{L-1} = (n-d+1, n+d-1): sp = 2N - 2 eps (outside [0, 2N] iff eps = -1, then sp = 2N+2).
Every site must be regular (in its range) or exceptional with the predicted value. Counts are printed.
"""
from multiprocessing import Pool
from collections import defaultdict
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    fr = oc.frame(w)
    N, D, n, d, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["eps"]
    L = n + d
    Lp = D + N
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
    hlast = (d, n - 1)
    vlast = (n - d + 1, n + d - 1)
    assert hlast in Hb and vlast in Vb
    for z in Hb:
        tp = N * z[0] - D * z[1]
        if oc.even_site(z):
            l = (z[0] + z[1]) // 2
            r = (2 * N * l) % Lp
            if r == 0:
                ok = tp == (Lp if eps == 1 else 0)
                out[("E1 even H exceptional, predicted", ok)] += 1
            else:
                ok = 1 <= tp <= Lp - 1
                out[("even H regular in range", ok)] += 1
        else:
            if z == hlast:
                ok = tp == D + eps
                out[("E2 odd H_last, predicted", ok)] += 1
            else:
                ok = N <= tp <= D
                out[("odd H regular in range", ok)] += 1
    for z in Vb:
        sp = (D + N) * z[0] + (D - N) * z[1]
        if oc.even_site(z):
            if z == vlast:
                out[("E4 even V_last, predicted", sp == 2 * N - 2 * eps)] += 1
            else:
                out[("even V regular in range", 0 <= sp <= 2 * N)] += 1
        else:
            l = (z[1] - z[0] + 1) // 2
            f = (D - N) * l - D * (-z[0])
            if f == 0 or f == D:
                pred = N - D if f == 0 else Lp
                out[("E3 odd V residue-0, predicted", sp == pred and ((f == 0) == (eps == 1)))] += 1
            else:
                out[("odd V regular in range", 2 - D + N <= sp <= Lp - 2)] += 1
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
