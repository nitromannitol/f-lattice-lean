"""Task 51: test the route to hC = (C(z0) >= 0) through the sheet facts of the conjugate packet.

For each even child (n,d), odd parent (D,N) with eps = N d - D n = +-1, 2D < d:
 z0 = seed point, L = d+n, T = d^2+2dn-n^2, C = D L + N (d-n).
 s0 = s(z0) (= T-2C-2n for eps=1, 2C-2n for eps=-1); h0(z0);
 whether s0 <= 2L-1 (the region where hEq / hGe of sheetFacts apply);
 whether h0(z0) == 0.
"""
import sys
from math import gcd
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 25

def h0(x, y):
    return (x * x + 2 * x * y - y * y - 2 * y - (x + y) % 2) // 4

def run():
    st = dict(pairs=0, s_in_region=0, h0_zero=0, h0_val={})
    for d in range(3, DMAX + 1, 2):
        for n in range(3, d, 2):
            if gcd(n, d) != 1:
                continue
            L, T = d + n, d * d + 2 * d * n - n * n
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
                    st['pairs'] += 1
                    K = 1 - (D + N) + (1 - W) * eps
                    x0 = eps * (d * K - D * (2 - L))
                    y0 = eps * (n * K - N * (2 - L))
                    s0 = L * x0 + (d - n) * y0
                    if s0 <= 2 * L - 1:
                        st['s_in_region'] += 1
                    v = h0(x0, y0)
                    st['h0_val'][(eps, v)] = st['h0_val'].get((eps, v), 0) + 1
                    if v == 0:
                        st['h0_zero'] += 1
    print(st)

run()
