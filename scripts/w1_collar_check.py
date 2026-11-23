#!/usr/bin/env python3
"""Numerical check (task 90, hsq): the off-collar lemma of W1_CONSTRUCTOR §1 on small children.

For a child n/d (odd n, d; d >= n + 2), with t = n x - d y, s = (d+n) x + (d-n) y, T = d^2 + 2dn - n^2, L = d + n:
  E-closed: closedRect (even: 2-T <= t <= L-2, 0 <= s <= T+2n; odd: n-T <= t <= d, 2-d+n <= s <= T+L-2);
  E° (strict): b-T < t < a, h < s < T+c (a,b,c,h parity-resolved: a=2/n, b=L-2/d, c=0/2-d+n, h=2n/L-2).
  freeH = {z in closed : z-(0,1) not in closed, t in H spectrum};  freeV = {z in closed : z-(1,0) not in closed, s in V spectrum}.
A collar point is a strict z within Chebyshev distance 1 of a vertex of freeH, freeV, and the translates (top, right) given by
  variant 'V+' (freeH+V, freeV+U), 'V-' (freeH-V, freeV-U), 'mixed' (freeH+V, freeV-U), 'mixed2' (freeH-V, freeV+U).
Claim: a strict z off the collar has every 8-neighbour (the corners of every unit square through z) strict.
"""
import sys
from itertools import product

def run(n, d, R=None):
    T = d * d + 2 * d * n - n * n
    L = d + n
    def ev(z): return (z[0] + z[1]) % 2 == 0
    def t(z): return n * z[0] - d * z[1]
    def s(z): return (d + n) * z[0] + (d - n) * z[1]
    def a(z): return 2 if ev(z) else n
    def b(z): return L - 2 if ev(z) else d
    def h(z): return 2 * n if ev(z) else L - 2
    def c(z): return 0 if ev(z) else 2 - d + n
    def closed(z):
        if ev(z):
            return 2 - T <= t(z) <= L - 2 and 0 <= s(z) <= T + 2 * n
        return n - T <= t(z) <= d and 2 - d + n <= s(z) <= T + L - 2
    def strict(z):
        return b(z) - T < t(z) < a(z) and h(z) < s(z) < T + c(z)
    def hspec(v):
        return (v % 2 == 0 and 2 <= v <= L - 2) or (v % 2 == 1 and n <= v <= d)
    def vspec(v):
        return v % 2 == 0 and ((0 <= v <= 2 * n) or (2 - d + n <= v <= L - 2))
    if R is None:
        R = 3 * L + 4
    pts = [(x, y) for x in range(-R, R + 1) for y in range(-R, R + 1)]
    freeH = {z for z in pts if closed(z) and not closed((z[0], z[1] - 1)) and hspec(t(z))}
    freeV = {z for z in pts if closed(z) and not closed((z[0] - 1, z[1])) and vspec(s(z))}
    U = (d, n)
    V = (n - d, d + n)
    arcs = {
        'V+': lambda: {(p[0] + V[0], p[1] + V[1]) for p in freeH} | {(p[0] + U[0], p[1] + U[1]) for p in freeV},
        'V-': lambda: {(p[0] - V[0], p[1] - V[1]) for p in freeH} | {(p[0] - U[0], p[1] - U[1]) for p in freeV},
        'mixed': lambda: {(p[0] + V[0], p[1] + V[1]) for p in freeH} | {(p[0] - U[0], p[1] - U[1]) for p in freeV},
        'mixed2': lambda: {(p[0] - V[0], p[1] - V[1]) for p in freeH} | {(p[0] + U[0], p[1] + U[1]) for p in freeV},
        'none': lambda: set(),
    }
    results = {}
    strictpts = [z for z in pts if strict(z)]
    for name, mk in arcs.items():
        verts = freeH | freeV | mk()
        bad = []
        for z in strictpts:
            near = any(max(abs(v[0] - z[0]), abs(v[1] - z[1])) <= 1 for v in verts) if verts else False
            if near:
                continue
            for dx, dy in product((-1, 0, 1), repeat=2):
                w = (z[0] + dx, z[1] + dy)
                if not strict(w):
                    bad.append((z, w))
                    break
            if len(bad) > 3:
                break
        results[name] = (len(strictpts), len(bad), bad[:2])
    return results

if __name__ == '__main__':
    for n, d in [(1, 3), (1, 5), (3, 5), (3, 7), (3, 9), (5, 7), (5, 9), (5, 11), (7, 9), (7, 13), (3, 11)]:
        res = run(n, d)
        print(f'n={n} d={d}', {k: (v[0], v[1]) for k, v in res.items()})
        for k, v in res.items():
            if v[1]:
                print('   ', k, 'counterexamples', v[2])
