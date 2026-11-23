"""Task 72 numerics: anchor coverage of the full price P z = F z - F(z - v) - eps pS z on each arc of E (|l|,|k| <= 10).
A field value F(w) is anchored if (F-own) some w + lV + kU is in the field's own strips, or (G-both) for w in E, its sheetMin
arguments are both anchored in the conjugate's own strips (F(w) = min(A, C)). F z on the arc: anchored at z itself (w = z in E).
Counts per arc: both F z and F(z - v) anchored, and the value P z - c0 in {0, -1} (checked where anchored).
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

R = 10


def own_field(P, w, n, d, L, T, V, U):
    def t(x): return n * x[0] - d * x[1]
    def s(x): return (d + n) * x[0] + (d - n) * x[1]
    for kk in range(-R, R + 1):
        for ll in range(-R, R + 1):
            q = (w[0] + ll * V[0] + kk * U[0], w[1] + ll * V[1] + kk * U[1])
            if 1 - d <= t(q) <= n + 2 * d - 1:
                return 0
            if 1 - 2 * d <= s(q) <= 2 * L - 1:
                return h0(q)
    return None


def run(u, st):
    P = ab.cc.params(tuple(u))
    Fch, _ = pl.standard(tuple(u))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    n, d, L, T = P['n'], P['d'], P['L'], P['T']
    n1, d1 = D - N, D + N
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
    lv = ((1 - W) * dq, (1 - W) * nq)
    e = (nq - dq + eps * dq, nq + dq + eps * nq)
    Tp = D * D + 2 * D * N - N * N
    c0 = (Tp - eps * (D + N)) // 2
    def pS(z): return N * z[0] - D * z[1]
    def fz_anchor(w):
        """Anchored value of the field at w (as a site of E, or any site): F-own first, then the sheet min via conj strips."""
        val = own_field(P, w, n, d, L, T, V, U)
        if val is not None:
            return ('F-own', val)
        if closed_E(P, w):
            a = (w[0] - lv[0], w[1] - lv[1])
            c = (a[0] - e[0], a[1] - e[1])
            ra = own_value(n1, d1, (-a[1], a[0] - 1))
            rc = own_value(n1, d1, (-c[1], c[0] - 1))
            if ra is not None and rc is not None:
                return ('G-both', None)
        return None
    M = 3 * (d + n) + 4
    for x0 in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x0, y0)
            if not closed_E(P, z):
                continue
            arc = arcs(P, z, closed_E)
            if arc is None:
                continue
            st[(arc, 'sites')] += 1
            fzA = fz_anchor(z)
            base = (z[0] - v[0], z[1] - v[1])
            fwA = own_field(P, base, n, d, L, T, V, U)
            if fwA is None:
                for kk in range(-R, R + 1):
                    for ll in range(-R, R + 1):
                        y = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                        if not closed_E(P, y):
                            continue
                        a = (y[0] - lv[0], y[1] - lv[1])
                        c = (a[0] - e[0], a[1] - e[1])
                        if own_value(n1, d1, (-a[1], a[0] - 1)) is not None and own_value(n1, d1, (-c[1], c[0] - 1)) is not None:
                            fwA = 'G-both'
                            break
                    if fwA is not None:
                        break
            st[(arc, 'F(z) anchored', fzA is not None)] += 1
            st[(arc, 'F(z-v) anchored', fwA is not None)] += 1
            if fzA is not None and fwA is not None:
                st[(arc, 'both_anchored')] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
