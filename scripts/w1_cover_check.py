"""Task 72 (cover): which lower bounds cover the price bound P z <= c0 at each arc site, by I1 / I2 and the exact strips.

Identities (verified below): g := F - h0.  (a) P z - c0 = g z - g (z - v).  (b) g is V-invariant (F and h0 have the same V-shift
t(x) + cV).  (c) g (y - kU) = g y - [h0 (y - kU) - h0 y]  (F is U-periodic, h0 shifts by (2 s + T - 2n)/4).
So for a representative y = z - v + lV + kU in E:  P z - c0 = g z - g y + [h0 (y - kU) - h0 y].
Sufficient for P z <= c0:  LB(g y) >= g z + [h0 (y - kU) - h0 y], with
  LB(g y) = min(LB A, LB C) - h0 y,
  LB C = h0 y  if eps = +1 and s y <= 2L - 1 (I2);  else 0 if t y >= 1 - d (I1);  else none;
          or the exact value of C (conjugate-strip band of C's argument) when that band applies;
  LB A = h0 y  if eps = -1 and s y <= 2L - 1 (I2);  or the exact value of A (band) when it applies; else none.
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
from w1_arc_anchor_check import own_field  # noqa: E402
from w1_bottom_conj_rep_check import own_value  # noqa: E402
from exact_quotient import words  # noqa: E402

R = 10


def exact_band_value(P, x, G):
    """Exact value of Fp(x) when its conjugate band applies: 'h0' -> 0 ; 'zero' -> h0(x) ; else None."""
    b = ab.band(P, x)
    if b in ('h0', 'both'):
        return 0
    if b == 'zero':
        return h0(x)
    return None


def run(u, st, detail):
    P = ab.cc.params(tuple(u))
    Fch, _ = pl.standard(tuple(u))
    G, _ = pl.standard(tuple(uac.conjWord(list(u))))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    n, d, L, T = P['n'], P['d'], P['L'], P['T']
    Tp = D * D + 2 * D * N - N * N
    c0 = (Tp - eps * (D + N)) // 2
    v = (eps * (N - D), eps * (N + D))
    V = (n - d, n + d)
    U = (d, n)
    lv = ((1 - W) * dq, (1 - W) * nq)
    e = (nq - dq + eps * dq, nq + dq + eps * nq)
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W

    def t(x): return n * x[0] - d * x[1]
    def s(x): return (d + n) * x[0] + (d - n) * x[1]
    def g(x): return Fch(x) - h0(x)
    def pS(z): return N * z[0] - D * z[1]
    def price(z): return Fch(z) - Fch((z[0] - v[0], z[1] - v[1])) - eps * pS(z)
    def Afun(y):
        Zx = (-(y[1] - lv[1]), (y[0] - lv[0]) - 1)
        return G(Zx) - h0(Zx)
    def Cfun(y):
        x = (y[0] - lv[0] - e[0], y[1] - lv[1] - e[1])
        Zx = (-x[1], x[0] - 1)
        return G(Zx) - h0(Zx) + nq * (y[0] - lv[0]) - dq * (y[1] - lv[1]) + ce

    M = 3 * (d + n) + 4
    for x0 in range(-M, M + 1):
        for y0 in range(-M, M + 1):
            z = (x0, y0)
            if not closed_E(P, z):
                continue
            arc = arcs(P, z, closed_E)
            if arc is None:
                continue
            base = (z[0] - v[0], z[1] - v[1])
            anchored = own_field(P, base, n, d, L, T, V, U) is not None
            if not anchored:
                for kk in range(-R, R + 1):
                    for ll in range(-R, R + 1):
                        y = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                        if closed_E(P, y):
                            a = (y[0] - lv[0], y[1] - lv[1])
                            c = (a[0] - e[0], a[1] - e[1])
                            if own_value(D - N, D + N, (-a[1], a[0] - 1)) is not None and \
                               own_value(D - N, D + N, (-c[1], c[0] - 1)) is not None:
                                anchored = True
                                break
                    if anchored:
                        break
            key = (arc, 'anchored' if anchored else 'UNANCHORED')
            st[key + ('sites',)] += 1
            # the sufficient criterion over all representatives
            good_I1 = good_I2 = good_any = False
            true_ok = True
            gz = g(z)
            for kk in range(-R, R + 1):
                for ll in range(-R, R + 1):
                    y = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                    if not closed_E(P, y):
                        continue
                    hy = h0(y)
                    delta = h0((y[0] - kk * U[0], y[1] - kk * U[1])) - hy
                    need = gz + delta
                    # true check (validates the identity): g y - need should equal -(P z - c0) >= 0
                    if g(y) - need != -(price(z) - c0):
                        true_ok = False
                    # lower bounds
                    a = (y[0] - lv[0], y[1] - lv[1])
                    c = (a[0] - e[0], a[1] - e[1])
                    LBA = None
                    LBC = None
                    if eps == -1 and s(y) <= 2 * L - 1:
                        LBA = hy
                    ea = exact_band_value(P, a, G)
                    if ea is not None:
                        LBA = ea if LBA is None else min(LBA, ea) if False else ea
                    LBC_I2 = (eps == 1 and s(y) <= 2 * L - 1)
                    if LBC_I2:
                        LBC = hy
                        used_c = 'I2'
                    elif t(y) >= 1 - d:
                        LBC = 0
                        used_c = 'I1'
                    ec = exact_band_value(P, c, G)
                    if ec is not None:
                        LBC = ec
                        used_c = 'strip'
                    if LBA is None or LBC is None:
                        continue
                    lb = min(LBA, LBC) - hy
                    if lb - need >= 0:
                        good_any = True
                        if (eps == 1 and LBC_I2) or (eps == -1 and LBA == hy):
                            good_I2 = True
                        else:
                            good_I1 = True
            st[key + ('true_identity_ok', true_ok)] += 1
            st[key + ('covered', good_any)] += 1
            if good_any:
                st[key + ('covered_via_I2', good_I2)] += 1
                st[key + ('covered_via_I1_or_strip_only', good_I1 and not good_I2)] += 1
            if detail is not None and not good_any:
                detail.append((tuple(u), z, arc, anchored))


if __name__ == '__main__':
    st = Counter()
    detail = []
    for w in words(3):
        run(w, st, detail)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)
