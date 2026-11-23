"""Task 72 numerics: the sheets via the CONJUGATE field G = standard(conjWord w) and its OWN strips.
Fp(x) = G(Zx) - h0(Zx), Zx = (-x2, x1 - 1). For the bottom arc site z and an E-representative y of z - v (y = z - v + lV + kU in E):
  A-arg = y - lv,  C-arg = y - lv - e   (e = V_q + eps U_q).
A value Fp(x) is exact when some w = Zx + l'V' + k'U' lies in G's own strips (conjugate child (n', d') = (D - N, D + N)):
  zero: 1 - d' <= t'(w) <= n' + 2d' - 1  -> G(w) = 0
  h0 : 1 - 2d' <= s'(w) <= 2L' - 1       -> G(w) = h0(w)
Reports, over bottom sites, whether some representative y has BOTH the A-arg and the C-arg exact.
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
from exact_quotient import words  # noqa: E402


def own_value(n1, d1, w):
    """Exact G(w) if w is in G's own strips with a representative w + l'V' + k'U', else None. Returns (value_of_G_at_w)."""
    L1 = d1 + n1
    T1 = d1 * d1 + 2 * d1 * n1 - n1 * n1
    V1 = (n1 - d1, n1 + d1)
    U1 = (d1, n1)
    def t1(x): return n1 * x[0] - d1 * x[1]
    def s1(x): return (d1 + n1) * x[0] + (d1 - n1) * x[1]
    for kk in range(-8, 9):
        for ll in range(-8, 9):
            q = (w[0] + ll * V1[0] + kk * U1[0], w[1] + ll * V1[1] + kk * U1[1])
            if 1 - d1 <= t1(q) <= n1 + 2 * d1 - 1:
                return (q, 'zero', 0)
            if 1 - 2 * d1 <= s1(q) <= 2 * L1 - 1:
                return (q, 'h0', h0(q))
    return None


def run(u, st):
    P = ab.cc.params(tuple(u))
    G, _ = pl.standard(tuple(uac.conjWord(list(u))))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    n, d = P['n'], P['d']
    n1, d1 = D - N, D + N  # conjugate child
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
    lv = ((1 - W) * dq, (1 - W) * nq)
    e = (nq - dq + eps * dq, nq + dq + eps * nq)
    M = 3 * (d + n) + 4
    for x0 in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x0, y0)
            if not closed_E(P, z) or arcs(P, z, closed_E) != 'bottom':
                continue
            base = (z[0] - v[0], z[1] - v[1])
            ok_both = False
            ok_a_any = False
            for kk in range(-6, 7):
                for ll in range(-6, 7):
                    y = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                    if not closed_E(P, y):
                        continue
                    a = (y[0] - lv[0], y[1] - lv[1])
                    c = (a[0] - e[0], a[1] - e[1])
                    ra = own_value(n1, d1, (-a[1], a[0] - 1))
                    rc = own_value(n1, d1, (-c[1], c[0] - 1))
                    if ra is not None:
                        ok_a_any = True
                    if ra is not None and rc is not None:
                        ok_both = True
            st['bottom'] += 1
            st[('A_exact_some_rep', ok_a_any)] += 1
            st[('A_and_C_exact_some_rep', ok_both)] += 1
            if (z[0], z[1]) == (1, 0):
                st[('H0', ok_both)] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
