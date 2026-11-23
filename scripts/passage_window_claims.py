"""Task 72 (FIXED_FREE §3-§4): test the claimed root boxes and middle windows against the actual routes, child by child.

Claims (FIXED_FREE_GAME_AUDIT §3, §4), with L = d+n, c = d-n, T = d^2+2dn-n^2, t = nx-dy, s = Lx+cy:
  H E-N (even root b, middle u=b+(1,0)):  root b: 2<=b1<=d-2, 0<=b2<=n-2;  middle: d+2<=t<=d+2n-2 (odd), L-2<s<T+2-c.
  H N-E-S (odd root b, middles b+(0,1), b+(1,1)):  root: 3<=b1<=d-2, 0<=b2<=n-1; first middle (even): 2-c<=t<=-2;
      second middle (odd): n+2-c<=t<=n-2;  both: L-2<s<T+2-c.
  V (all V middles): -T+L-1 < t < 0.
  V N-W (odd root, middle z+(0,1) even): root: b1>=n-d+2, b2<=L-3; middle: 2n+2<=s<=2d-2 (claimed).
  V W-N-E (even root): root b1>=n-d+1, b2<=L-3, 2<=s_b<=2n-2;  first middle (odd): 2-L<=s<=-c-2;
      second middle (even): 2-2n<=s<=-2.
Each claim is tested for every route of every child with d <= DMAX.
"""
import math, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from free_site_exclusions import curves, add, sub
from passage_windows import route_moves

def run(dmax=21):
    fails = {}
    counts = {}
    def check(name, ok, info):
        counts[name] = counts.get(name, 0) + 1
        if not ok:
            fails.setdefault(name, []).append(info)
    for d in range(3, dmax + 1, 2):
        for n in range(1, d, 2):
            if math.gcd(n, d) != 1 or n + 2 > d:
                continue
            L, c, T = d + n, d - n, d * d + 2 * d * n - n * n
            def tg(z): return n * z[0] - d * z[1]
            def sg(z): return L * z[0] + c * z[1]
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
                    zpar = sum(z) % 2 == 0
                    if kind == 'H' and rtype == 'EN':
                        b = z
                        check('H-EN root box', 2 <= b[0] <= d - 2 and 0 <= b[1] <= n - 2, (n, d, b))
                        u = path[1]
                        check('H-EN middle t', d + 2 <= tg(u) <= d + 2 * n - 2, (n, d, u, tg(u)))
                        check('H-EN middle s', L - 2 < sg(u) < T + 2 - c, (n, d, u, sg(u)))
                    if kind == 'H' and rtype == 'NES':
                        b = z
                        check('H-NES root box', 3 <= b[0] <= d - 2 and 0 <= b[1] <= n - 1, (n, d, b))
                        m1, m2 = path[1], path[2]
                        check('H-NES middle1 t', 2 - c <= tg(m1) <= -2, (n, d, m1, tg(m1)))
                        check('H-NES middle2 t', n + 2 - c <= tg(m2) <= n - 2, (n, d, m2, tg(m2)))
                        check('H-NES middle1 s', L - 2 < sg(m1) < T + 2 - c, (n, d, m1, sg(m1)))
                        check('H-NES middle2 s', L - 2 < sg(m2) < T + 2 - c, (n, d, m2, sg(m2)))
                    if kind == 'V':
                        for u in path[1:-1]:
                            check('V middle t', -T + L - 1 < tg(u) < 0, (n, d, u, tg(u)))
                        if rtype == 'NW':
                            b = z
                            check('V-NW root', b[0] >= n - d + 2 and b[1] <= L - 3, (n, d, b))
                            m = path[1]
                            check('V-NW middle s', 2 * n + 2 <= sg(m) <= 2 * d - 2, (n, d, m, sg(m)))
                        if rtype == 'WNE':
                            b = z
                            check('V-WNE root box', b[0] >= n - d + 1 and b[1] <= L - 3, (n, d, b))
                            check('V-WNE root s', 2 <= sg(b) <= 2 * n - 2, (n, d, b, sg(b)))
                            m1, m2 = path[1], path[2]
                            check('V-WNE middle1 s', 2 - L <= sg(m1) <= -c - 2, (n, d, m1, sg(m1)))
                            check('V-WNE middle2 s', 2 - 2 * n <= sg(m2) <= -2, (n, d, m2, sg(m2)))
    return counts, fails

if __name__ == "__main__":
    counts, fails = run(int(sys.argv[1]) if len(sys.argv) > 1 else 21)
    for k in sorted(counts):
        print(f"{k}: checks {counts[k]}, failures {len(fails.get(k, []))}", fails.get(k, [])[:2])
