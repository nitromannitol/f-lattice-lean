"""Task 72 numerics: on the bottom arc, the band of z - v in the field's OWN strips (child frame: zero clause in t, h0 clause in s).
F z = 0 on pure bottom (zero strip of z). Then P z = -F(z - v) - eps pS(z). Classify z - v:
  'zero': 1 - d <= t(z - v) <= n + 2d - 1   -> F(z - v) = 0
  'h0'  : 1 - 2d <= s(z - v) <= 2L - 1       -> F(z - v) = h0(z - v)
  'none'
and compare the predicted P with the actual P - c0 in {0, -1}.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import importlib.util
import permit_local as pl  # noqa: E402
import w1_arc_band_check as ab  # noqa: E402
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_arc_band_check import arcs  # noqa: E402
from w1_sheet_check import h0  # noqa: E402
from exact_quotient import words  # noqa: E402


def run(u, st):
    P = ab.cc.params(tuple(u))
    Fch, _ = pl.standard(tuple(u))
    eps, N, D = P['eps'], P['N'], P['D']
    n, d, L = P['n'], P['d'], P['L']
    v = (eps * (N - D), eps * (N + D))
    Tp = D * D + 2 * D * N - N * N
    c0 = (Tp - eps * (D + N)) // 2
    def t(x): return n * x[0] - d * x[1]
    def s(x): return (d + n) * x[0] + (d - n) * x[1]
    def pS(z): return N * z[0] - D * z[1]
    def price(z): return Fch(z) - Fch((z[0] - v[0], z[1] - v[1])) - eps * pS(z)
    M = 3 * (d + n) + 4
    for x0 in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x0, y0)
            if not closed_E(P, z) or arcs(P, z, closed_E) != 'bottom':
                continue
            w = (z[0] - v[0], z[1] - v[1])
            tw, sw = t(w), s(w)
            if 1 - d <= tw <= n + 2 * d - 1:
                cls = 'zero'
                Fw = 0
            elif 1 - 2 * d <= sw <= 2 * L - 1:
                cls = 'h0'
                Fw = h0(w)
            else:
                cls = 'none'
                Fw = None
            pz = price(z) - c0
            st[(cls, 'P-c0', pz)] += 1
            st[('sites', cls)] += 1
            if Fw is not None:
                pred = -Fw - eps * pS(z) + (Fch(z)) - c0
                st[(cls, 'predicted_eq_actual', pred == pz)] += 1
            if (x0, y0) == (1, 0):
                st[('H0', cls, pz)] += 1
            # which bottom sites have P=c0 (pz==0)?
            if pz == 0:
                st[('P=c0 site', z)] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
