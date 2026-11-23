"""Task 72 numerics: for each bottom-arc site z, the representatives y = z - v + lV + kU in E (small range), and whether the
sheet arguments are in a strip of the conjugate:
  a-arg  = y - lv          (A(y) = Fp(a-arg))
  x-arg  = y - lv - V_q    (C(y) = Fp(x-arg - eps U_q) + ..., paragraph 5: Fp(x - eps U_q) = Fp(x) + c0' - P'(Zx))
Band of Fp(x): 'h0' -> Fp = 0 ; 'zero' -> Fp = h0(x) ; 'none' -> outside.
Counts: sites with a representative whose a-arg AND x-arg are both banded ('both-banded'), and sites with a banded a-arg only.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import importlib.util
import w1_arc_band_check as ab  # noqa: E402
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_arc_band_check import arcs  # noqa: E402
from exact_quotient import words  # noqa: E402


def fp_band(P, x):
    b = ab.band(P, x)
    if b == 'h0' or b == 'both':
        return 0
    if b == 'zero':
        return 'h0'
    return None


def run(u, st):
    P = ab.cc.params(tuple(u))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    n, d = P['n'], P['d']
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
    lv = ((1 - W) * dq, (1 - W) * nq)
    Vq = (nq - dq, nq + dq)
    M = 3 * (d + n) + 4
    for x0 in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x0, y0)
            if not closed_E(P, z) or arcs(P, z, closed_E) != 'bottom':
                continue
            base = (z[0] - v[0], z[1] - v[1])
            best = None
            reps = 0
            for kk in range(-6, 7):
                for ll in range(-6, 7):
                    yy = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                    if not closed_E(P, yy):
                        continue
                    reps += 1
                    ax = (yy[0] - lv[0], yy[1] - lv[1])
                    xx = (ax[0] - Vq[0], ax[1] - Vq[1])
                    fa = fp_band(P, ax)
                    fx = fp_band(P, xx)
                    key = ('a', fa is not None, 'x', fx is not None)
                    if best is None or (key[1] and key[3]):
                        if best is None or (fa is not None and fx is not None):
                            best = key
                    st[key] += 1
            st['sites'] += 1
            if best is None:
                st['no_rep'] += 1
            elif best[1] and best[3]:
                st['has_both_banded_rep'] += 1
            elif best[1]:
                st['has_a_banded_rep_only'] += 1
            else:
                st['no_banded_a_rep'] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
