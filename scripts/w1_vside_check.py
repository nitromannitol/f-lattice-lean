"""Task 51 (V side of W1 section 2): numeric check of the parent s-ranges of the V-side query.

W1_CONSTRUCTOR section 2 (V side): r is in the left collar with
  even r:  L - T <= t(r) <= 0,  2n < s(r) <= 2L - 2;      odd r:  d - T < t(r) <= n - 2,  L - 2 < s(r) <= 3d + n - 2.
For the parent query (W0: sp(y - Vq) = sp(r) - 2; W1: sp(I - (y - Vq)) = sp(r)) the archive claims the parent s*
satisfies  even: 2N <= s* < 2 Lp;   odd: Lp - 2 < s* < 3D + N,   with sp(x) = (D+N) x1 + (D-N) x2, Lp = D + N.
Here y = z - W U and r = z (W0) or r = R - z (W1), R = U + V + I; we enumerate r directly and compute s* from the
parent query as the archive states it. Points: all lattice points r with the stated t,s ranges.
"""
import sys
from math import gcd
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 21

def run():
    st = dict(pairs=0, even_pts=0, even_bad=0, odd_pts=0, odd_bad=0, ex=[])
    for d in range(3, DMAX + 1, 2):
        for n in range(3, d, 2):
            if gcd(n, d) != 1:
                continue
            L, T = d + n, d * d + 2 * d * n - n * n
            B = 3 * (d + n) + 10
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
                    Lp = D + N
                    Vq = (nq - dq, dq + nq)
                    V = (n - d, d + n)
                    U = (d, n)
                    for r1 in range(-B, B + 1):
                        for r2 in range(-B, B + 1):
                            t = n * r1 - d * r2
                            s = L * r1 + (d - n) * r2
                            even = (r1 + r2) % 2 == 0
                            if even:
                                if not (L - T <= t <= 0 and 2 * n < s <= 2 * L - 2):
                                    continue
                            else:
                                if not (d - T < t <= n - 2 and L - 2 < s <= 3 * d + n - 2):
                                    continue
                            # parent query s-coordinate, as the archive states it
                            if W == 0:
                                # sp(y - Vq) = sp(r) - 2, with y = r (W0)
                                sstar = (Lp) * (r1 - Vq[0]) + (D - N) * (r2 - Vq[1])
                            else:
                                # W1: y = r ... use r = R - z; the archive's identity sp(I - (y - Vq)) = sp(r)
                                # evaluated directly at the query point I - (y - Vq) with y = (I + V - r) (z = R - r, y = z - U)
                                yx, yy = (1 + V[0] - r1, -1 + V[1] - r2)
                                qx, qy = (1 - (yx - Vq[0]), -1 - (yy - Vq[1]))
                                sstar = Lp * qx + (D - N) * qy
                            if even:
                                st['even_pts'] += 1
                                if not (2 * N <= sstar < 2 * Lp):
                                    st['even_bad'] += 1
                                    if len(st['ex']) < 6:
                                        st['ex'].append(('even', n, d, D, N, eps, (r1, r2), t, s, sstar))
                            else:
                                st['odd_pts'] += 1
                                if not (Lp - 2 < sstar < 3 * D + N):
                                    st['odd_bad'] += 1
                                    if len(st['ex']) < 6:
                                        st['ex'].append(('odd', n, d, D, N, eps, (r1, r2), t, s, sstar))
    print(st, flush=True)

run()
