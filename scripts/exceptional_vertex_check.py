"""Task 72 (c): is V_p + I (W = 1) the free V site vLast of the earlier frame, and is its prescribed direction west?

Earlier frame: child fraction n/d = N/D (the odd parent of the current child). Lean (S3FreeBoundary, Sheets, ChildFrame):
  L = d + n, periodDenominator T = d^2 + 2dn - n^2, tGrade(x) = n x1 - d x2, sGrade(x) = L x1 + (d - n) x2,
  closedPolygon E: even z: 2 - T <= t <= d + n - 2 and 0 <= s <= T + 2n;  odd z: n - T <= t <= d, 2 - d + n <= s <= T + d + n - 2,
  freeV = {z in E, (z1-1, z2) not in E, vSpectrum(s(z))}, vSpectrum(s): s even and (0 <= s <= 2n or 2-d+n <= s <= L-2),
  vLast = (n - d + 1, n + d - 1) = V_p + I with V_p = (N - D, N + D), prescribedV eta vLast = (eta, 0) (east for eta = 1).
  Sign for W = 1 (eps = +1) : the policy's west input at vLast is incomingNeg = (x-1, y), i.e. direction (-1, 0): eta = -1.
"""
from math import gcd

def T(n, d):
    return d * d + 2 * d * n - n * n

def tg(n, d, x):
    return n * x[0] - d * x[1]

def sg(n, d, x):
    return (d + n) * x[0] + (d - n) * x[1]

def even(x):
    return (x[0] + x[1]) % 2 == 0

def in_E(n, d, z):
    t = tg(n, d, z); s = sg(n, d, z); Tn = T(n, d)
    if even(z):
        return 2 - Tn <= t <= d + n - 2 and 0 <= s <= Tn + 2 * n
    return n - Tn <= t <= d and 2 - d + n <= s <= Tn + d + n - 2

def v_spectrum(n, d, s):
    return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= d + n - 2))

def free_V(n, d, z):
    return in_E(n, d, z) and not in_E(n, d, (z[0] - 1, z[1])) and v_spectrum(n, d, sg(n, d, z))

def run(bound=60):
    total = 0; in_freeV = []; not_free = []
    for D in range(2, bound + 1):
        for N in range(1, D):
            if gcd(N, D) != 1 or (N + D) % 2 == 0:      # odd proper parent N/D
                continue
            n, d = N, D                                    # earlier child = parent
            vLast = (N - D + 1, N + D - 1)                 # V_p + I
            total += 1
            (in_freeV if free_V(n, d, vLast) else not_free).append((N, D, vLast, even(vLast), in_E(n, d, vLast)))
    return total, in_freeV, not_free

if __name__ == "__main__":
    total, yes, no = run()
    print("odd proper parents N/D checked:", total)
    print("V_p + I is in freeV (earlier frame):", len(yes))
    print("V_p + I is NOT in freeV:", len(no))
    for row in no[:10]:
        print("  not free: parent", row[0], "/", row[1], "vLast", row[2], "even", row[3], "in E", row[4])
    for row in yes[:6]:
        print("  free: parent", row[0], "/", row[1], "vLast", row[2])
