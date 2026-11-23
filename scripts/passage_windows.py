"""Task 72 (FIXED_FREE §3-§4): the (t, s) grade windows of the short-passage middles and roots, measured on the actual routes.

For each odd coprime child n/d with n + 2 <= d (d <= DMAX) and each consecutive pair of the H curve or V curve (routes.py),
records the route type, the parity of the start, and the (t, s) grades of the root and of each interior middle.
Prints min/max per (kind, route type, role) to compare with the windows claimed in FIXED_FREE_GAME_AUDIT §3 and §4.
"""
import math, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from free_site_exclusions import curves, add, sub

def grades(n, d, z):
    return (n * z[0] - d * z[1], (d + n) * z[0] + (d - n) * z[1])

def route_moves(kind, z, dest):
    step = sub(dest, z)
    if kind == 'H':
        if sum(z) % 2 == 0:
            return [(1, 0)] if step == (1, 0) else [(1, 0), (0, 1)], ('E' if step == (1, 0) else 'EN')
        return [(0, 1), (1, 0), (0, -1)], 'NES'
    if sum(z) % 2:
        return ([(0, 1)], 'N') if step == (0, 1) else ([(0, 1), (-1, 0)], 'NW')
    return [(-1, 0), (0, 1), (1, 0)], 'WNE'

def main(dmax=31):
    rec = {}
    for d in range(3, dmax + 1, 2):
        for n in range(1, d, 2):
            if math.gcd(n, d) != 1 or n + 2 > d:
                continue
            H, V = curves(n, d)
            for kind, curve in (('H', H), ('V', V)):
                for i in range(1, len(curve) - 1):          # skip the first (terminal) vertex, as routes.py
                    z, dest = curve[i], curve[i + 1]
                    moves, rtype = route_moves(kind, z, dest)
                    path = [z]
                    for e in moves:
                        path.append(add(path[-1], e))
                    if path[-1] != dest:
                        continue
                    par = 'even' if sum(z) % 2 == 0 else 'odd'
                    tz, sz = grades(n, d, z)
                    rec.setdefault((kind, rtype, par, 'root'), []).append((tz, sz, n, d))
                    for k, u in enumerate(path[1:-1]):
                        tu, su = grades(n, d, u)
                        upar = 'even' if sum(u) % 2 == 0 else 'odd'
                        rec.setdefault((kind, rtype, upar, 'middle', k), []).append((tu, su, n, d))
    return rec

if __name__ == "__main__":
    rec = main(int(sys.argv[1]) if len(sys.argv) > 1 else 21)
    for key in sorted(rec, key=str):
        rows = rec[key]
        ts = [r[0] for r in rows]; ss = [r[1] for r in rows]
        # express the s-window relative to L-2 and T+2-c, and the t-window
        print(key, 'count', len(rows), 't in', (min(ts), max(ts)), 's in', (min(ss), max(ss)))
