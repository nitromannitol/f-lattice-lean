"""Task 72 (nonfree bridge): numeric check of the two candidate definitions of 'nonfree' for an odd child n/d.

Lean definitions (W1Constructor, Q3Exit, S3FreeBoundary, Sheets, ChildFrame), for the child n/d with n, d odd and n + 2 <= d:
  T = d^2 + 2dn - n^2,  t(z) = n x - d y,  s(z) = (d+n) x + (d-n) y,  deck span {iK + jV}, K = (d, n), V = (n-d, n+d)
  t(K) = 0, s(K) = T, t(V) = -T, s(V) = 0.
  E (closedPolygon): even z: 2-T <= t <= d+n-2, 0 <= s <= T+2n;  odd z: n-T <= t <= d, 2-d+n <= s <= T+d+n-2.
  StrictInterior (W1): even: d+n-2-T < t < 2, 2n < s < T;  odd: d-T < t < n, d+n-2 < s < T+2-d+n.
  hSpectrum(t): (t even, 2 <= t <= d+n-2) or (t odd, n <= t <= d).   vSpectrum(s): s even and (0 <= s <= 2n or 2-d+n <= s <= d+n-2).
  onBoundarySpectrum(z): exists k in {-1,0,1}: hSpectrum(t + kT) or vSpectrum(s + kT).
  freeH: z in E, (x, y-1) not in E, hSpectrum(t(z)).   freeV: z in E, (x-1, y) not in E, vSpectrum(s(z)).
Candidate A ("nonfree" = no deck translate of z is in E and on a boundary spectrum).
Candidate B ("nonfree" = no deck translate of z is in freeH or freeV, the wording of the note).
Bridge claim: nonfree z -> some deck translate of z is in StrictInterior.
"""
from math import gcd

def run(n, d, box=12, R=4):
    T = d*d + 2*d*n - n*n
    def even(z): return (z[0] + z[1]) % 2 == 0
    def t(z): return n*z[0] - d*z[1]
    def s(z): return (d+n)*z[0] + (d-n)*z[1]
    def inE(z):
        if even(z):
            return 2 - T <= t(z) <= d+n-2 and 0 <= s(z) <= T + 2*n
        return n - T <= t(z) <= d and 2 - d + n <= s(z) <= T + d + n - 2
    def inSI(z):
        if even(z):
            return d + n - 2 - T < t(z) < 2 and 2*n < s(z) < T
        return d - T < t(z) < n and d + n - 2 < s(z) < T + 2 - d + n
    def hS(x): return (x % 2 == 0 and 2 <= x <= d+n-2) or (x % 2 == 1 and n <= x <= d)
    def vS(x): return x % 2 == 0 and ((0 <= x <= 2*n) or (2 - d + n <= x <= d + n - 2))
    def onBS(z):
        return any(hS(t(z) + k*T) or vS(s(z) + k*T) for k in (-1, 0, 1))
    def freeH(z): return inE(z) and not inE((z[0], z[1]-1)) and hS(t(z))
    def freeV(z): return inE(z) and not inE((z[0]-1, z[1])) and vS(s(z))
    # deck translates by i K + j V
    K = (d, n); V = (n-d, n+d)
    vecs = [(i*K[0] + j*V[0], i*K[1] + j*V[1]) for i in range(-R, R+1) for j in range(-R, R+1)]
    def trans(z): return [(z[0]+v[0], z[1]+v[1]) for v in vecs]
    failA = []; failB = []
    for x in range(-box, box+1):
        for y in range(-box, box+1):
            w = (x, y)
            tr = trans(w)
            if not any(inSI(u) for u in tr):
                if not any(inE(u) and onBS(u) for u in tr):
                    failA.append(w)          # candidate A nonfree, but no SI translate
                if not any(freeH(u) or freeV(u) for u in tr):
                    failB.append(w)          # candidate B nonfree, but no SI translate
    return failA, failB

if __name__ == "__main__":
    total = 0; bad_A = []; bad_B = []
    for d in range(3, 22, 2):
        for n in range(1, d - 1, 2):
            if gcd(n, d) != 1 or n + 2 > d:
                continue
            total += 1
            A, B = run(n, d)
            if A: bad_A.append((n, d, len(A), A[:3]))
            if B: bad_B.append((n, d, len(B), B[:3]))
    print("odd children checked:", total)
    print("candidate A (no translate on E and boundary spectrum) fails to bridge for:", len(bad_A), "children")
    for row in bad_A[:5]: print("   child", row[0], "/", row[1], "bad sites", row[2], row[3])
    print("candidate B (no translate in freeH or freeV) fails to bridge for:", len(bad_B), "children")
    for row in bad_B[:5]: print("   child", row[0], "/", row[1], "bad sites", row[2], row[3])
