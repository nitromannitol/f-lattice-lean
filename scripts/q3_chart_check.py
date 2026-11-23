"""Task 59 paragraph 4 (the common primary chart), words <= 4, PROVISIONAL readings.

For each black centre z in E, each input u of z, and eta = +-1, with p = z + eta sigma, q = u + eta sigma
(sigma = shortShift), keep the pairs whose shifted transverse grades stay in the supported interval
[a_chi - T, b_chi] (chi = parity of each end). For those pairs:
  (a) separation: NOT (one of s(p), s(q) strictly below lam and the other strictly above mu), with
      lam = 2 - d + n (odd V lower endpoint), mu = 2n (even V upper endpoint); mu - lam = L - 2.
  (b) gap: |s(q) - s(p)| <= L always (one input changes s by at most L).
  (c) 0 < s(U_p) = 2C < T (the paragraph's "since 0 < s(U_p) < T").
  (d) the common shift: which of eta*sigma (= eta eps U_p) or -eta eps U_q makes the pair q - p ... is reported only as
      the values s(p), s(q) and the shift vectors; the chart definition is not fixed by the text, so (d) is a count, not a test.
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
    L = n + d
    C = D * L + N * (d - n)
    sig = (2 * eps * D, 2 * eps * N)
    tg = lambda z: n * z[0] - d * z[1]
    sg = lambda z: L * z[0] + (d - n) * z[1]
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    out = defaultdict(int)
    out[("c: 0 < 2C < T", 0 < 2 * C < T)] += 1
    for z in reps:
        if pl.lap(F, z) != -1:
            continue
        for u in (oc.incoming_neg(z), oc.incoming_pos(z)):
            for eta in (1, -1):
                p = (z[0] + eta * sig[0], z[1] + eta * sig[1])
                q = (u[0] + eta * sig[0], u[1] + eta * sig[1])
                def supported(y, yp):
                    a, b = (2, L - 2) if oc.even_site(y) else (n, d)
                    return a - T <= tg(yp) <= b
                if not (supported(z, p) and supported(u, q)):
                    out[("pairs with transverse exit", True)] += 1
                    continue
                out[("pairs inside supported interval", True)] += 1
                sp, sq = sg(p), sg(q)
                lam, mu = 2 - d + n, 2 * n
                sep1 = sp < lam and sq > mu
                sep2 = sq < lam and sp > mu
                out[("(a) separation failures", sep1 or sep2)] += 1
                out[("(b) |s(q)-s(p)| <= L", abs(sq - sp) <= L)] += 1
                out[("parity of s(p), s(q) even", sp % 2 == 0 and sq % 2 == 0)] += 1
                if sep1 or sep2:
                    out[("smallest failing example", (w, z, u, eta, sp, sq))] += 0
    return out


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    with Pool(12) as pool:
        for out in pool.imap_unordered(run, ws):
            for k, v in out.items():
                tot[k] += v
    for k in sorted(tot, key=str):
        if not (isinstance(k, tuple) and k and k[0] == "smallest failing example"):
            print(k, tot[k], flush=True)
