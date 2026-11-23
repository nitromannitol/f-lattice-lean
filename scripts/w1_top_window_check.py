"""Task 49 numerics: the parent query x = y - eps U - (1-W)(d_q,n_q) of the top collar (W1_CONSTRUCTOR section 2).

For every even child (n,d) (n,d odd, coprime, n<d, d<=DMAX), every odd parent (D,N) with eps = N d - D n = +-1 and
D < d/2 (so d_q = d - 2D >= 1), and every lattice point y in the claimed top-collar ranges:
  even y: L-2 < t(y) <= 2L-2 and 2n < s(y) < T;   odd y: d < t(y) <= n+2d-2 and L-2 < s(y) < T+2-d+n,
checks (1) tp(x) = tp(y) - W, (2) odd y: 1-D <= tp(x) <= N+2D-1 (ordinary zero strip, StrongEstimates.zeroStripInterval),
(3) even y: 1-(D+N) <= tp(x) <= 2(D+N)-1 (strengthened even window, named input).
Also counts the points tested. Coordinates: t = n x - d y, s = L x + (d-n) y, L = d+n, T = d^2+2dn-n^2,
tp(z) = N z1 - D z2, parity = (z1+z2) mod 2 (E-site convention of the note: even sites are (x+y) even).
"""
import sys
from math import gcd

DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15

def run():
    tot = {'odd_pts': 0, 'odd_bad': 0, 'even_pts': 0, 'even_bad': 0, 'W_bad': 0}
    bad_examples = []
    parents_seen = 0
    for d in range(3, DMAX + 1, 2):
        for n in range(1, d, 2):
            if gcd(n, d) != 1:
                continue
            L, T = d + n, d * d + 2 * d * n - n * n
            B = 3 * (d + n) + 10
            for eps in (1, -1):
                W = (1 + eps) // 2
                for D in range(1, d):
                    if 2 * D >= d:
                        break
                    num = eps + D * n
                    if num % d != 0:
                        continue
                    N = num // d
                    parents_seen += 1
                    Lp = D + N
                    for x1 in range(-B, B + 1):
                        for x2 in range(-B, B + 1):
                            t = n * x1 - d * x2
                            s = L * x1 + (d - n) * x2
                            even = (x1 + x2) % 2 == 0
                            if even:
                                if not (L - 2 < t <= 2 * L - 2 and 2 * n < s < T):
                                    continue
                            else:
                                if not (d < t <= n + 2 * d - 2 and L - 2 < s < T + 2 - d + n):
                                    continue
                            # the query x = y - eps U - (1-W)(d_q, n_q), with d_q = d - 2D, n_q = n - 2N
                            dq, nq = d - 2 * D, n - 2 * N
                            xq1 = x1 - eps * d - (1 - W) * dq
                            xq2 = x2 - eps * n - (1 - W) * nq
                            tp_y = N * x1 - D * x2
                            tp_x = N * xq1 - D * xq2
                            if tp_x != tp_y - W:
                                tot['W_bad'] += 1
                            if even:
                                tot['even_pts'] += 1
                                ok = (1 - Lp <= tp_x <= 2 * Lp - 1)
                                if not ok:
                                    tot['even_bad'] += 1
                                    if len(bad_examples) < 8:
                                        bad_examples.append(('even', n, d, D, N, eps, (x1, x2), t, s, tp_x))
                            else:
                                tot['odd_pts'] += 1
                                ok = (1 - D <= tp_x <= N + 2 * D - 1)
                                if not ok:
                                    tot['odd_bad'] += 1
                                    if len(bad_examples) < 8:
                                        bad_examples.append(('odd', n, d, D, N, eps, (x1, x2), t, s, tp_x))
    print('parent pairs', parents_seen, tot)
    for e in bad_examples:
        print('  bad', e)

run()
