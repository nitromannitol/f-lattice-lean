"""Task 72 numerics: for each bottom-arc site z, does some representative w = (z - v) + lV + kU lie in the FIELD'S OWN strip
(zero clause in t: 1 - d <= t(w) <= n + 2d - 1 ; h0 clause in s: 1 - 2d <= s(w) <= 2L - 1)? If yes, F(z - v) is exact by
field_rep_formula: F(z - v) = F(w) + (-l) t(w) - T (l(l+1)/2) - l cV  with F(w) = 0 (zero) or h0(w) (h0).
Check the predicted P z = -F(z - v) - eps pS(z) (F z = 0 on the pure bottom arc) against the actual price.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
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
    n, d, L, T = P['n'], P['d'], P['L'], P['T']
    assert (d + n + T) % 2 == 0
    cV = -(d + n + T) // 2
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
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
            base = (z[0] - v[0], z[1] - v[1])
            found = None
            for kk in range(-8, 9):
                for ll in range(-8, 9):
                    w = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                    if 1 - d <= t(w) <= n + 2 * d - 1:
                        found = (ll, kk, w, 'zero', 0)
                        break
                    if 1 - 2 * d <= s(w) <= 2 * L - 1:
                        found = (ll, kk, w, 'h0', h0(w))
                        break
                if found:
                    break
            if found is None:
                st['no_own_rep'] += 1
                continue
            ll, kk, w, cls, Fw = found
            pred_Fbase = Fw + (-ll) * t(w) - T * ((-ll) * (-ll - 1) // 2) + (-ll) * cV
            st[('rep_formula_ok', pred_Fbase == Fch(base))] += 1
            pred_P = -pred_Fbase - eps * pS(z) + Fch(z)
            st[('own_rep', cls)] += 1
            st[('pred_P_matches', pred_P == price(z))] += 1
            st[('P-c0', price(z) - c0, cls)] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
