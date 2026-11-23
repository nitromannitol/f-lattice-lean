ALL_COLOURS = True
REQUIRE_IN_E = True
"""Task 59 step 2, Q3 paragraph 4 window bounds (PROVISIONAL readings from Q2.md paragraph 3):
transverse grade t (tGrade), longitudinal s; supported interval at parity chi = [a_chi - T, b_chi] with
(a_e, b_e) = (2, L-2), (a_o, b_o) = (n, d); the two ends are the black center z and an input u of z; the shifted edge is
(z + eta sigma, u + eta sigma), sigma = shortShift, eta = +-1; t(y + eta sigma) = t(y) - 2 eta.
Exits of a site y: upper if t(y + eta sigma) > b_chi(y); lower if t(y + eta sigma) < a_chi(y) - T.
Claims tested (words <= 4), for each black center z, input u of z, eta, and exiting end y in {z, u}:
  C0  n >= 3 holds (the paper's hypothesis).
  C1  upper exit: t(z), t(u) in [-1, L-2].
  C2  upper exit: t(z+eta sigma), t(u+eta sigma) in [1-d, n+2d-1] (ordinary zero strip).
  C3  lower exit: t(z)+T, t(u)+T in [2, n+1+d].
  C4  lower exit: t(z+eta sigma)+T, t(u+eta sigma)+T in [1-d, n+2d-1] (zero strip after the transverse translate).
Counts per claim: holds / fails, with the first failing example printed (for the report).
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
    sig = (2 * eps * D, 2 * eps * N)
    tg = lambda z: n * z[0] - d * z[1]
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    out = defaultdict(int)
    examples = {}
    def check(name, ok, info):
        out[(name, ok)] += 1
        if not ok and name not in examples:
            examples[name] = info
    out[("C0 n >= 3", n >= 3)] += 1
    out[("edges checked", "u in E")] += 0
    for z in reps:
        if ALL_COLOURS is False and pl.lap(F, z) != -1:
            continue
        for u in (oc.incoming_neg(z), oc.incoming_pos(z)):
            if REQUIRE_IN_E and not inE(u):
                continue
            for eta in (1, -1):
                for y in (z, u):
                    yp = (y[0] + eta * sig[0], y[1] + eta * sig[1])
                    chi_e = oc.even_site(y)
                    a, b = (2, L - 2) if chi_e else (n, d)
                    ty, typ = tg(y), tg(yp)
                    if typ > b:  # upper exit
                        check("C1 upper: t(z),t(u) in [-1,L-2]", -1 <= tg(z) <= L - 2 and -1 <= tg(u) <= L - 2,
                              (w, z, u, eta, y, tg(z), tg(u)))
                        zs = (z[0] + eta * sig[0], z[1] + eta * sig[1])
                        us = (u[0] + eta * sig[0], u[1] + eta * sig[1])
                        check("C2 upper: shifted in zero strip", 1 - d <= tg(zs) <= n + 2 * d - 1 and 1 - d <= tg(us) <= n + 2 * d - 1,
                              (w, z, u, eta, y, tg(zs), tg(us)))
                    if typ < a - T:  # lower exit
                        check("C3 lower: t+T of ends in [2,n+1+d]", 2 <= tg(z) + T <= n + 1 + d and 2 <= tg(u) + T <= n + 1 + d,
                              (w, z, u, eta, y, tg(z) + T, tg(u) + T))
                        zs = (z[0] + eta * sig[0], z[1] + eta * sig[1])
                        us = (u[0] + eta * sig[0], u[1] + eta * sig[1])
                        check("C4 lower: shifted+T in zero strip", 1 - d <= tg(zs) + T <= n + 2 * d - 1 and 1 - d <= tg(us) + T <= n + 2 * d - 1,
                              (w, z, u, eta, y, tg(zs) + T, tg(us) + T))
    return out, examples


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    ex = {}
    with Pool(12) as pool:
        for out, examples in pool.imap_unordered(run, ws):
            for k, v in out.items():
                tot[k] += v
            for k, v in examples.items():
                ex.setdefault(k, v)
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
    for k, v in ex.items():
        print("first failure", k, v, flush=True)
