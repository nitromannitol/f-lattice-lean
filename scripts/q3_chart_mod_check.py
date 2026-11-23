"""Task 59 paragraph 4, the common primary chart taken modulo s(U_p) = 2C (words <= 4, PROVISIONAL readings).

A common shift v applied to both shifted ends changes both s-values by s(v). The chart is the window
[lam, lam + 2C) with lam = 2 - d + n, taken modulo 2C (U_p is a period: sigma = eps U_p shifts s by 2 eta eps C).
For each black centre z, input u, eta, with both shifted ends inside the supported interval, test:
  (0) no shift: floor((s(p)-lam)/2C) == floor((s(q)-lam)/2C);
  (1) common shift v = -eta eps U_q (s(v) = -eta eps s(U_q)): the same test on s(p)+s(v), s(q)+s(v);
  (2) either (0) or (1) holds.
Counts, and the smallest failing pair if (2) fails.
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    fr = oc.frame(w)
    N, D, n, d, T, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"], fr["eps"]
    nq, dq = fr["nq"], fr["dq"]
    L = n + d
    C = D * L + N * (d - n)
    per = 2 * C
    lam = 2 - d + n
    sig = (2 * eps * D, 2 * eps * N)
    Uq = (dq, nq)
    tg = lambda z: n * z[0] - d * z[1]
    sg = lambda z: L * z[0] + (d - n) * z[1]
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    out = defaultdict(int)
    ex = None
    sUq = sg(Uq)
    for z in reps:
        if pl.lap(F, z) != -1:
            continue
        for u in (oc.incoming_neg(z), oc.incoming_pos(z)):
            for eta in (1, -1):
                p = (z[0] + eta * sig[0], z[1] + eta * sig[1])
                q = (u[0] + eta * sig[0], u[1] + eta * sig[1])
                def sup(y, yp):
                    a, b = (2, L - 2) if oc.even_site(y) else (n, d)
                    return a - T <= tg(yp) <= b
                if not (sup(z, p) and sup(u, q)):
                    continue
                sp, sq = sg(p), sg(q)
                same = lambda a, b: (a - lam) // per == (b - lam) // per
                ok0 = same(sp, sq)
                sv = -eta * eps * sUq
                ok1 = same(sp + sv, sq + sv)
                out[("(0) no shift", ok0)] += 1
                out[("(1) shift -eta eps Uq", ok1)] += 1
                out[("(2) (0) or (1)", ok0 or ok1)] += 1
                if not (ok0 or ok1) and ex is None:
                    ex = (w, z, u, eta, p, q, sp, sq, sv)
    return out, ex


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    exs = []
    with Pool(12) as pool:
        for out, ex in pool.imap_unordered(run, ws):
            for k, v in out.items():
                tot[k] += v
            if ex is not None:
                exs.append(ex)
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
    exs.sort(key=lambda e: (len(e[0]), e[0]))
    print("smallest failing", exs[:2], flush=True)
