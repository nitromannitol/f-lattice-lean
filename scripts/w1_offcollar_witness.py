#!/usr/bin/env python3
"""Task 90 (hsq): the off-collar witness table of W1_CONSTRUCTOR §1, checked on all coprime odd children with d >= n+2 (n <= 11, d <= 21).

Children n/d (n, d odd, coprime). t = n x - d y, s = (d+n) x + (d-n) y, T = d^2 + 2dn - n^2, L = d + n.
closedRect (even z: 2-T <= t <= L-2, 0 <= s <= T+2n; odd z: n-T <= t <= d, 2-d+n <= s <= T+L-2).
StrictInterior (even z: L-2-T < t < 2, 2n < s < T; odd z: d-T < t < n, L-2 < s < T+2-d+n).
Arcs: freeH = {v in closedRect, v-(0,1) outside, t in H spectrum}; freeV = {v in closedRect, v-(1,0) outside, s in V spectrum};
collar vertices: freeH, freeV, freeH + V (top), freeV + U (right), with U = (d,n), V = (n-d, d+n).

Witness table: if a strict z has an 8-neighbour w outside the strict interior, the violated edge of w (A: t(w) >= a(w);
B: t(w) <= b(w)-T; C: s(w) <= h(w); D: s(w) >= T+c(w)) and the parity of z select a fixed block offset delta with
z+delta in the arc of the violated edge:
  A: freeH,  delta = (1,-1) if z even, (0,-1) if z odd
  B: freeH+V, delta = (-1,1) if z even, (0,1) if z odd
  C: freeV,  delta = (-1,0) if z even, (-1,-1) if z odd
  D: freeV+U, delta = (1,0) if z even, (1,1) if z odd
This script checks the table (membership of z+delta in the arc of its type) on all such instances.
"""
from math import gcd
from itertools import product
from collections import Counter


def setup(n, d):
    T = d * d + 2 * d * n - n * n
    L = d + n
    ev = lambda z: (z[0] + z[1]) % 2 == 0
    t = lambda z: n * z[0] - d * z[1]
    s = lambda z: (d + n) * z[0] + (d - n) * z[1]
    a = lambda z: 2 if ev(z) else n
    b = lambda z: L - 2 if ev(z) else d
    h = lambda z: 2 * n if ev(z) else L - 2
    c = lambda z: 0 if ev(z) else 2 - d + n

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

    U = (d, n)
    V = (n - d, d + n)

    def isarc(v, kind):
        if kind == 'A':
            return closed(v) and not closed((v[0], v[1] - 1)) and hspec(t(v))
        if kind == 'B':
            u = (v[0] - V[0], v[1] - V[1])
            return closed(u) and not closed((u[0], u[1] - 1)) and hspec(t(u))
        if kind == 'C':
            return closed(v) and not closed((v[0] - 1, v[1])) and vspec(s(v))
        u = (v[0] - U[0], v[1] - U[1])
        return closed(u) and not closed((u[0] - 1, u[1])) and vspec(s(u))

    return dict(T=T, L=L, ev=ev, t=t, s=s, a=a, b=b, h=h, c=c, strict=strict, isarc=isarc)


def violated(S, w):
    out = []
    if not S['t'](w) < S['a'](w):
        out.append('A')
    if not S['b'](w) - S['T'] < S['t'](w):
        out.append('B')
    if not S['h'](w) < S['s'](w):
        out.append('C')
    if not S['s'](w) < S['T'] + S['c'](w):
        out.append('D')
    return out


WIT = {('A', 'even'): (1, -1), ('A', 'odd'): (0, -1), ('B', 'even'): (-1, 1), ('B', 'odd'): (0, 1),
       ('C', 'even'): (-1, 0), ('C', 'odd'): (-1, -1), ('D', 'even'): (1, 0), ('D', 'odd'): (1, 1)}


def main():
    pairs = [(n, d) for n in range(1, 12, 2) for d in range(n + 2, 22, 2) if gcd(n, d) == 1]
    offsets = list(product((-1, 0, 1), repeat=2))
    total, bad = Counter(), Counter()
    for n, d in pairs:
        S = setup(n, d)
        R = 3 * S['L'] + 4
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                z = (x, y)
                if not S['strict'](z):
                    continue
                par = 'even' if S['ev'](z) else 'odd'
                for dx, dy in offsets:
                    w = (x + dx, y + dy)
                    if S['strict'](w):
                        continue
                    for typ in violated(S, w):
                        total[(typ, par)] += 1
                        ox, oy = WIT[(typ, par)]
                        if not S['isarc']((x + ox, y + oy), typ):
                            bad[(typ, par)] += 1
    print('children', len(pairs), 'instances', sum(total.values()), 'failures', sum(bad.values()))


if __name__ == '__main__':
    main()
