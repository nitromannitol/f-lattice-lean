"""Diagnostic for unanchored bottom sites: at each representative y, the true values A(y)-h0(y), C(y)-h0(y), g(y), the need
g z + delta, which lower bounds are available (I1: t y >= 1-d ; I2: s y <= 2L-1 ; strip: exact band), and the true slack g y - need."""
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
from w1_cover_check import exact_band_value  # noqa: E402
from exact_quotient import words  # noqa: E402

R = 10


def main(limit_words):
    st = Counter()
    shown = 0
    for u in words(3):
        P = ab.cc.params(tuple(u))
        Fch, _ = pl.standard(tuple(u))
        G, _ = pl.standard(tuple(uac.conjWord(list(u))))
        eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
        n, d, L, T = P['n'], P['d'], P['L'], P['T']
        Tp = D * D + 2 * D * N - N * N
        c0 = (Tp - eps * (D + N)) // 2
        v = (eps * (N - D), eps * (N + D))
        V = (n - d, n + d); U = (d, n)
        lv = ((1 - W) * dq, (1 - W) * nq)
        e = (nq - dq + eps * dq, nq + dq + eps * nq)
        Tq = dq * dq + 2 * dq * nq - nq * nq
        ce = (Tq - dq - nq) // 2 + 2 * W
        def t(x): return n * x[0] - d * x[1]
        def s(x): return (d + n) * x[0] + (d - n) * x[1]
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
                if not closed_E(P, z) or arcs(P, z, closed_E) != 'bottom':
                    continue
                base = (z[0] - v[0], z[1] - v[1])
                if own_field(P, base, n, d, L, T, V, U) is not None:
                    continue  # anchored by the field's own strips
                gz = Fch(z) - h0(z)
                st['unanch_bottom'] += 1
                rows = []
                for kk in range(-R, R + 1):
                    for ll in range(-R, R + 1):
                        y = (base[0] + ll * V[0] + kk * U[0], base[1] + ll * V[1] + kk * U[1])
                        if not closed_E(P, y):
                            continue
                        hy = h0(y)
                        delta = h0((y[0] - kk * U[0], y[1] - kk * U[1])) - hy
                        need = gz + delta
                        gy = Fch(y) - hy
                        Ay = Afun(y) - hy
                        Cy = Cfun(y) - hy
                        I1 = t(y) >= 1 - d
                        I2 = s(y) <= 2 * L - 1
                        a = (y[0] - lv[0], y[1] - lv[1]); c = (a[0] - e[0], a[1] - e[1])
                        sA = exact_band_value(P, a, G) is not None
                        sC = exact_band_value(P, c, G) is not None
                        rows.append((kk, ll, eps, I1, I2, sA, sC, need, gy, gy - need, Ay, Cy))
                if not rows:
                    st['no_rep'] += 1
                    continue
                best = max(rows, key=lambda r: r[9])
                st[('best_true_slack', best[9])] += 1
                st[('eps', eps, 'I1_avail_some_rep', any(r[3] for r in rows))] += 1
                st[('eps', eps, 'I2_avail_some_rep', any(r[4] for r in rows))] += 1
                st[('eps', eps, 'strip_A_some_rep', any(r[5] for r in rows))] += 1
                st[('eps', eps, 'strip_C_some_rep', any(r[6] for r in rows))] += 1
                if shown < limit_words:
                    shown += 1
                    print('word', u, 'z', z, 'eps', eps, 'h0z', h0(z), 'gz', gz, 'Pz-c0', price(z) - c0, flush=True)
                    for r in rows[:6]:
                        print('   rep k,l', r[0], r[1], 'I1', r[3], 'I2', r[4], 'stripA', r[5], 'stripC', r[6],
                              'need', r[7], 'g(y)', r[8], 'slack', r[9], 'A-h0', r[10], 'C-h0', r[11], flush=True)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)


if __name__ == '__main__':
    main(4)
