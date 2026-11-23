"""Task 72 (FIXED_FREE §3-§4): the root hypotheses of the short-passage nonfree lemmas, checked on the actual routes.

  H E-N   (even root z, middle z+(1,0)):   z in E, c+2 <= t(z), s(z) < T+2-2d.
  H N-E-S (odd root z, middles z+(0,1), z+(1,1)):   n+2 <= t(z) <= d-2,  2n-2 < s(z) < T+2-3d+n.
  V N-W   (odd root z, middle z+(0,1)):   2n+2-c <= s(z) <= L-2,  L-1-T+d < t(z) < d.
  V W-N-E (even root z, middles z+(-1,0), z+(-1,1)):   2 <= s(z) <= 2n-2,  2L-1-T < t(z) < n.
"""
import math, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from free_site_exclusions import curves, add, sub
from passage_windows import route_moves

def main(dmax=21):
    res = {}
    for d in range(3, dmax + 1, 2):
        for n in range(1, d, 2):
            if math.gcd(n, d) != 1 or n + 2 > d:
                continue
            L, c, T = d + n, d - n, d * d + 2 * d * n - n * n
            t = lambda z: n * z[0] - d * z[1]
            s = lambda z: L * z[0] + c * z[1]
            def E_even(z):
                return 2 - T <= t(z) <= L - 2 and 0 <= s(z) <= T + 2 * n
            def E_odd(z):
                return n - T <= t(z) <= d and 2 - c <= s(z) <= T + L - 2
            H, V = curves(n, d)
            for kind, curve in (('H', H), ('V', V)):
                for i in range(1, len(curve) - 1):
                    z, dest = curve[i], curve[i + 1]
                    moves, rtype = route_moves(kind, z, dest)
                    path = [z]
                    for e in moves:
                        path.append(add(path[-1], e))
                    if path[-1] != dest:
                        continue
                    key = (kind, rtype)
                    def rec(name, ok):
                        res.setdefault(name, [0, 0])
                        res[name][0] += 1
                        if not ok:
                            res[name][1] += 1
                    if key == ('H', 'EN'):
                        rec('H-EN: z in E', E_even(z))
                        rec('H-EN: c+2 <= t(z)', c + 2 <= t(z))
                        rec('H-EN: s(z) < T+2-2d', s(z) < T + 2 - 2 * d)
                    if key == ('H', 'NES'):
                        rec('H-NES: n+2 <= t(z) <= d-2', n + 2 <= t(z) <= d - 2)
                        rec('H-NES: 2n-2 < s(z) < T+2-3d+n', 2 * n - 2 < s(z) < T + 2 - 3 * d + n)
                    if key == ('V', 'NW'):
                        rec('V-NW: 2n+2-c <= s(z) <= L-2', 2 * n + 2 - c <= s(z) <= L - 2)
                        rec('V-NW: L-1-T+d < t(z) < d', L - 1 - T + d < t(z) < d)
                    if key == ('V', 'WNE'):
                        rec('V-WNE: 2 <= s(z) <= 2n-2', 2 <= s(z) <= 2 * n - 2)
                        rec('V-WNE: 2L-1-T < t(z) < n', 2 * L - 1 - T < t(z) < n)
    return res

if __name__ == "__main__":
    res = main(int(sys.argv[1]) if len(sys.argv) > 1 else 21)
    for k in sorted(res):
        print(f"{k}: routes {res[k][0]}, failures {res[k][1]}")
