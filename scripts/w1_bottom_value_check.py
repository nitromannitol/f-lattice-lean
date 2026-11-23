"""Task 72 numerics: the bottom-arc value. On the pure bottom arc F z = 0, so P z = c0 - h0 z - g z with g z = F(z - v) - h0(z - v).
Checks (proper words, length <= 3): which bottom sites have P = c0 (expected: H0 only), and at each bottom site the representative
y = z - v + lV + kU in E with F(z - v) = F(y) + (-l) t(y) - T (-l)(-l-1)/2 + (-l) cV (field_rep_formula), F(y) = min(A(y), C(y)).
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import importlib.util
import permit_local as pl  # noqa: E402
import upper_attainment_check as uac  # noqa: E402
_sv = sys.argv
sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', str(Path(__file__).parent / 'w1_collar_check.py'))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)
sys.argv = _sv
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_arc_band_check import arcs  # noqa: E402
from w1_sheet_check import h0  # noqa: E402
from exact_quotient import words  # noqa: E402


def run(u, st, rows):
    P = cc.params(tuple(u))
    Fch, _ = pl.standard(tuple(u))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    n, d, T = P['n'], P['d'], P['T']
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
    cV = None
    # c_V = (-(d + n + T))/2 from coherentConstantV_eq (2 cV = -(d + n + T))
    assert (d + n + T) % 2 == 0
    cV = -(d + n + T) // 2
    Tq = dq * dq + 2 * dq * nq - nq * nq
    # cutPrice c0 = (T_p - eps (D + N))/2, T_p = D^2 + 2 D N - N^2
    Tp = D * D + 2 * D * N - N * N
    c0 = (Tp - eps * (D + N)) // 2
    def pS(z):
        return N * z[0] - D * z[1]
    def price(z):
        return Fch(z) - Fch((z[0] - v[0], z[1] - v[1])) - eps * pS(z)
    M = 3 * (d + n) + 4
    for x in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x, y0)
            if not closed_E(P, z):
                continue
            if arcs(P, z, closed_E) != 'bottom':
                continue
            pz = price(z)
            st['bottom'] += 1
            st[('P_minus_c0', pz - c0)] += 1
            # representative: search l, k with y = z - v + l V + k U in E
            base = (z[0] - v[0], z[1] - v[1])
            rep = None
            for kk in range(-8, 9):
                for ll in range(-8, 9):
                    yy = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                    if closed_E(P, yy):
                        rep = (ll, kk, yy)
                        break
                if rep:
                    break
            if rep is None:
                st['no_rep'] += 1
                continue
            ll, kk, yy = rep
            tY = n * yy[0] - d * yy[1]
            # field_rep_formula: F(x) = F(y) + (-l) t(y) - T((-l)(-l-1)/2) + (-l) cV
            pred = Fch(yy) + (-ll) * tY - T * ((-ll) * (-ll - 1) // 2) + (-ll) * cV
            st[('rep_formula_ok', pred == Fch(base))] += 1
            rows.append((tuple(u), z, pz - c0, rep))


if __name__ == '__main__':
    st = Counter()
    rows = []
    for w in words(3):
        run(w, st, rows)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
