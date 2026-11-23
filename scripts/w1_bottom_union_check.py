"""Task 72 numerics: union of the two anchor types over a wider representative range (|l|, |k| <= 12):
  (F-own)  some w = z - v + lV + kU lies in the field's own strips (exact F(z - v) via field_rep_formula), or
  (G-both) some E-representative y of z - v has both sheet arguments (A-arg, C-arg) exact via the conjugate's own strips.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import permit_local as pl  # noqa: E402
import upper_attainment_check as uac  # noqa: E402
import w1_arc_band_check as ab  # noqa: E402
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_arc_band_check import arcs  # noqa: E402
from w1_sheet_check import h0  # noqa: E402
from w1_bottom_conj_rep_check import own_value  # noqa: E402
from exact_quotient import words  # noqa: E402

R = 12


def run(u, st):
    P = ab.cc.params(tuple(u))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    n, d, L = P['n'], P['d'], P['L']
    n1, d1 = D - N, D + N
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
    lv = ((1 - W) * dq, (1 - W) * nq)
    e = (nq - dq + eps * dq, nq + dq + eps * nq)
    def t(x): return n * x[0] - d * x[1]
    def s(x): return (d + n) * x[0] + (d - n) * x[1]
    M = 3 * (d + n) + 4
    for x0 in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x0, y0)
            if not closed_E(P, z) or arcs(P, z, closed_E) != 'bottom':
                continue
            base = (z[0] - v[0], z[1] - v[1])
            anchor = None
            for kk in range(-R, R + 1):
                for ll in range(-R, R + 1):
                    w = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                    if 1 - d <= t(w) <= n + 2 * d - 1 or 1 - 2 * d <= s(w) <= 2 * L - 1:
                        anchor = 'F-own'
                        break
                    if anchor:
                        break
                if anchor:
                    break
            if anchor is None:
                for kk in range(-R, R + 1):
                    for ll in range(-R, R + 1):
                        y = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                        if not closed_E(P, y):
                            continue
                        a = (y[0] - lv[0], y[1] - lv[1])
                        c = (a[0] - e[0], a[1] - e[1])
                        if own_value(n1, d1, (-a[1], a[0] - 1)) is not None and own_value(n1, d1, (-c[1], c[0] - 1)) is not None:
                            anchor = 'G-both'
                            break
                    if anchor:
                        break
            st[('anchor', anchor)] += 1
            st['bottom'] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
