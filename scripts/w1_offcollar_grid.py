#!/usr/bin/env python3
"""Task 90 (hsq): is the off-collar witness table a statement about (t, s) alone?

All conditions of the collar witnesses are linear in the grades (t, s), with the parity of t fixed by the site parity (n, d odd) and s
always even. This script enumerates ALL integer pairs (t, s) with that parity (no lattice constraint) for a child n/d and checks the
uniform witness table on every strict (t, s) with a violated outside neighbour. A pass means the off-collar lemma needs no lattice
argument for that child; a failure marks where the coprimality (lattice) argument is needed.
"""
import sys
from itertools import product


def check(n, d, span=None):
    T = d * d + 2 * d * n - n * n
    L = d + n
    B = span if span is not None else 3 * L + 3 * T // 2 + 6
    # block offsets with (dt, ds, parity flip)
    off = [(dx, dy) for dx, dy in product((-1, 0, 1), repeat=2) if (dx, dy) != (0, 0)]
    dtds = {(dx, dy): (n * dx - d * dy, (d + n) * dx + (d - n) * dy) for dx, dy in off}
    WIT = {('A', 0): (1, -1), ('A', 1): (0, -1), ('B', 0): (-1, 1), ('B', 1): (0, 1),
           ('C', 0): (-1, 0), ('C', 1): (-1, -1), ('D', 0): (1, 0), ('D', 1): (1, 1)}
    # membership in the arcs, in (t, s) coordinates
    def closed(par, t, s):  # par = 0 even, 1 odd
        if par == 0:
            return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
        return n - T <= t <= d and 2 - d + n <= s <= T + L - 2

    def hspec(t):
        return (t % 2 == 0 and 2 <= t <= L - 2) or (t % 2 == 1 and n <= t <= d)

    def vspec(s):
        return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= L - 2))

    def arc(kind, t, s, par):
        # the witness point v has parity par, grades (t, s)
        if kind == 'A':  # freeH at v
            return closed(par, t, s) and not closed(1 - par, t + d, s - (d - n)) and hspec(t)
        if kind == 'B':  # freeH at u = v - V:  t(u) = t + T, s(u) = s
            tu, su, pu = t + T, s, par
            return closed(pu, tu, su) and not closed(1 - pu, tu + d, su - (d - n)) and hspec(tu)
        if kind == 'C':  # freeV at v
            return closed(par, t, s) and not closed(1 - par, t - n, s - L) and vspec(s)
        # D: freeV at u = v - U: t(u) = t, s(u) = s - T
        tu, su, pu = t, s - T, par
        return closed(pu, tu, su) and not closed(1 - pu, tu - n, su - L) and vspec(su)

    def strict(par, t, s):
        if par == 0:
            return d + n - 2 - T < t < 2 and 2 * n < s < T
        return d - T < t < n and L - 2 < s < T + 2 - d + n

    fails = {}
    total = 0
    for par in (0, 1):
        for t in range(-B, B + 1):
            if t % 2 != par:
                continue
            for s in range(-B, B + 1):
                if s % 2 != 0:
                    continue
                if not strict(par, t, s):
                    continue
                for (dx, dy), (dt, ds) in dtds.items():
                    tw, sw = t + dt, s + ds
                    pw = par ^ ((dx + dy) % 2)
                    viol = []
                    # A: t(w) >= a(w); a = 2 (even) or n (odd)
                    aw = 2 if pw == 0 else n
                    if tw >= aw: viol.append('A')
                    bw = L - 2 if pw == 0 else d
                    if tw <= bw - T: viol.append('B')
                    hw = 2 * n if pw == 0 else L - 2
                    if sw <= hw: viol.append('C')
                    cw = 0 if pw == 0 else 2 - d + n
                    if sw >= T + cw: viol.append('D')
                    for kind in viol:
                        total += 1
                        ox, oy = WIT[(kind, par)]
                        # witness offset in (t, s)
                        wt = t + n * ox - d * oy
                        ws = s + (d + n) * ox + (d - n) * oy
                        if not arc(kind, wt, ws, 1 - par if (ox + oy) % 2 else par):
                            fails.setdefault((kind, par), []).append((t, s, (dx, dy)))
    return total, fails


if __name__ == '__main__':
    for n, d in [(1, 3), (1, 5), (3, 5), (3, 7), (5, 7), (5, 9), (3, 9), (3, 11), (5, 11), (7, 9)]:
        total, fails = check(n, d)
        print(f'n={n} d={d} instances={total} failing (type,parity): ',
              {k: len(v) for k, v in fails.items()})
        for k, v in list(fails.items())[:2]:
            print('    e.g.', k, v[:3])
