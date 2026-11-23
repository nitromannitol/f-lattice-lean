"""Check, from the Lean definitions, the staircase box of the free H and V traces and the root windows used by the route theorems.

Definitions mirrored (ChildFrame, S3FreeBoundary, Sheets.closedPolygon, W1Constructor.closedRect), with n = num, d = den,
L = d + n, c = d - n, T = d^2 + 2dn - n^2, t(z) = n x - d y, s(z) = L x + c y:
  closedPolygon: even z: 2-T <= t <= L-2 and 0 <= s <= T+2n;  odd z: n-T <= t <= d and 2-d+n <= s <= T+d+n-2.
  freeH: z in E, (x, y-1) not in E, hSpectrum t;  freeV: z in E, (x-1, y) not in E, vSpectrum s.
  hSpectrum t: (t even, 2 <= t <= L-2) or (t odd, n <= t <= d).  vSpectrum s: s even and ((0<=s<=2n) or (2-d+n<=s<=L-2)).
Children: gcd(n,d)=1, n+2 <= d, L even (so n, d odd).
Output: the box violations, and the extreme root windows over all free sites of each parity."""
import math, sys

def children(dmax):
    for d in range(3, dmax + 1):
        for n in range(1, d - 1):
            if n + 2 <= d and (n + d) % 2 == 0 and math.gcd(n, d) == 1:
                yield n, d

def run(dmax):
    box_bad = []
    summary = {}
    for n, d in children(dmax):
        L, c = d + n, d - n
        T = d * d + 2 * d * n - n * n
        def t_of(x, y): return n * x - d * y
        def s_of(x, y): return L * x + c * y
        def inE(x, y):
            t, s = t_of(x, y), s_of(x, y)
            if (x + y) % 2 == 0:
                return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
            return n - T <= t <= d and 2 - d + n <= s <= T + d + n - 2
        def hS(t):
            return (t % 2 == 0 and 2 <= t <= L - 2) or (t % 2 == 1 and n <= t <= d)
        def vS(s):
            return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= L - 2))
        R = 3 * (d + n) + 4
        win = {}
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                if not inE(x, y):
                    continue
                t, s = t_of(x, y), s_of(x, y)
                if hS(t) and not inE(x, y - 1):
                    if not (1 <= x <= d and 0 <= y <= n - 1):
                        box_bad.append(("H", n, d, (x, y)))
                    key = ("H", (x + y) % 2 == 0)
                    lo = win.setdefault(key, [t, t, s, s])
                    lo[0] = min(lo[0], t); lo[1] = max(lo[1], t); lo[2] = min(lo[2], s); lo[3] = max(lo[3], s)
                if vS(s) and not inE(x - 1, y):
                    key = ("V", (x + y) % 2 == 0)
                    lo = win.setdefault(key, [t, t, s, s])
                    lo[0] = min(lo[0], t); lo[1] = max(lo[1], t); lo[2] = min(lo[2], s); lo[3] = max(lo[3], s)
        summary[(n, d)] = (T, win)
    return box_bad, summary

if __name__ == "__main__":
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    bad, summary = run(dmax)
    print("children:", len(summary), "H-box violations:", len(bad), bad[:5])
    for (n, d), (T, win) in sorted(summary.items(), key=lambda kv: kv[0][1])[:12]:
        print((n, d), "T", T, {k: v for k, v in sorted(win.items())})
