"""Task 72 (FIXED_FREE §3-§4): does spectral avoidance alone exclude the middles?

A middle u is nonfree if, for every deck translate v = iK + jV (t(v) = -jT, s(v) = iT), u + v is not in freeH (needs
hSpectrum(t) and the bottom boundary) nor in freeV (needs vSpectrum(s) and the left boundary). The spectral part is:
  (A) for all j: not hSpectrum(t(u) - jT);   (B) for all i: not vSpectrum(s(u) + iT).
This script tests (A) and (B) for every middle of every passage (routes.py) and reports which middles violate them.
"""
import math, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from free_site_exclusions import curves, add, sub
from passage_windows import route_moves

def hspec(n, d, x):
    return (x % 2 == 0 and 2 <= x <= d + n - 2) or (x % 2 == 1 and n <= x <= d)

def vspec(n, d, x):
    return x % 2 == 0 and ((0 <= x <= 2 * n) or (2 - d + n <= x <= d + n - 2))

def avoids(n, d, t, s, T):
    # translates t - jT and s + iT; search a window large enough (the spectra lie in [-T, 2T] after shifting)
    for j in range(-6, 7):
        if hspec(n, d, t - j * T):
            return False, ('H', j)
    for i in range(-6, 7):
        if vspec(n, d, s + i * T):
            return False, ('V', i)
    return True, None

def run(dmax=21):
    bad = {}
    tot = {}
    for d in range(3, dmax + 1, 2):
        for n in range(1, d, 2):
            if math.gcd(n, d) != 1 or n + 2 > d:
                continue
            L, c, T = d + n, d - n, d * d + 2 * d * n - n * n
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
                    for k, u in enumerate(path[1:-1]):
                        t = n * u[0] - d * u[1]
                        s = L * u[0] + c * u[1]
                        ok, why = avoids(n, d, t, s, T)
                        key = (kind, rtype, 'even' if sum(u) % 2 == 0 else 'odd', k)
                        tot[key] = tot.get(key, 0) + 1
                        if not ok:
                            bad.setdefault(key, []).append((n, d, u, t, s, why))
    return tot, bad

if __name__ == "__main__":
    tot, bad = run(int(sys.argv[1]) if len(sys.argv) > 1 else 21)
    for k in sorted(tot):
        print(k, 'middles', tot[k], 'spectral violations', len(bad.get(k, [])), bad.get(k, [])[:2])
