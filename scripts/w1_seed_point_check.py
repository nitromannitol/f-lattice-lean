"""Task 50 numerics: the even seed point z0 of the child (n,d) with odd parent P=(D,N), even parent Q=(dq,nq), eps = N d - D n.

z0 is the unique integer solution of t(z0) = 2 - L and t_p(z0 - lv) = 1 - (D+N), where t = n x - d y, t_p = N x - D y, lv = (1-W) Uq.
Checks, for every proper even child (n,d) with n >= 3 and every odd parent with 2D < d, 1 <= N <= D or N >= 0, N d - D n = +-1:
 (1) z0 is even, lies in the closed polygon (0 <= s(z0) <= T + 2n, t in range), and s(z0) = T - 2C - 2n (eps=+1), 2C - 2n (eps=-1);
 (2) the parent point w = z0 - lv - e (e = Vq + eps Uq) has s_p(w) inside the ordinary h0 strip [1-2D, 2(D+N)-1];
 (3) the second-branch value C(z0) = h0(w) + a_q(z0 - lv) + c_e equals 0 or 1 (archive: fC = 1, exceptional 0).
"""
import sys
from math import gcd

DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 25

def h0(x, y):
    return (x * x + 2 * x * y - y * y - 2 * y - (x + y) % 2) // 4

def run():
    stats = dict(pairs=0, inside_E_bad=0, s_formula_bad=0, even_bad=0, strip_out=0, C_values={})
    for d in range(3, DMAX + 1, 2):
        for n in range(3, d, 2):
            if gcd(n, d) != 1:
                continue
            L, T = d + n, d * d + 2 * d * n - n * n
            C_child = None
            for eps in (1, -1):
                W = (1 + eps) // 2
                for D in range(1, d):
                    if 2 * D >= d:
                        break
                    if (eps + D * n) % d:
                        continue
                    N = (eps + D * n) // d
                    if N < 0 or N > D:
                        continue
                    dq, nq = d - 2 * D, n - 2 * N
                    if dq < 1 or nq < 0:
                        continue
                    stats['pairs'] += 1
                    C = D * L + N * (d - n)
                    Tq = dq * dq + 2 * dq * nq - nq * nq
                    K = 1 - (D + N) + (1 - W) * eps  # N x - D y = K
                    x0 = eps * (d * K - D * (2 - L))
                    y0 = eps * (n * K - N * (2 - L))
                    # checks: t and t_p
                    assert n * x0 - d * y0 == 2 - L
                    assert N * (x0 - (1 - W) * dq) - D * (y0 - (1 - W) * nq) == 1 - (D + N)
                    if (x0 + y0) % 2 != 0:
                        stats['even_bad'] += 1
                    s0 = L * x0 + (d - n) * y0
                    if not (0 <= s0 <= T + 2 * n):
                        stats['inside_E_bad'] += 1
                    expect = (T - 2 * C - 2 * n) if eps == 1 else (2 * C - 2 * n)
                    if s0 != expect:
                        stats['s_formula_bad'] += 1
                    lvx, lvy = (1 - W) * dq, (1 - W) * nq
                    ex, ey = (nq - dq) + eps * dq, (dq + nq) + eps * nq
                    wx, wy = x0 - lvx - ex, y0 - lvy - ey
                    sp = (D + N) * wx + (D - N) * wy
                    Lp = D + N
                    if not (1 - 2 * D <= sp <= 2 * Lp - 1):
                        stats['strip_out'] += 1
                    ce = (Tq - dq - nq) // 2 + 2 * W
                    val = h0(wx, wy) + nq * (x0 - lvx) - dq * (y0 - lvy) + ce
                    stats['C_values'][val] = stats['C_values'].get(val, 0) + 1
    print(stats)

run()
