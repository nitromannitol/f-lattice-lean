#!/usr/bin/env python3
"""Task 90 (hsq): a lattice-free witness table indexed by the violating offset.

For a child n/d and every (t, s) in the strict range (parity-compatible, no lattice constraint), and every outside 8-neighbour w = z + delta,
the set of block points e (including e = 0) with z + e an arc vertex of the collar (freeH, freeV, freeH + V, freeV + U) is computed.
Group by (delta, violation pattern of w, parity of z) and intersect. A non-empty intersection in every group gives a witness depending
only on (delta, pattern, parity), so the off-collar lemma needs no lattice argument for that child.
"""
import sys
from itertools import product
from collections import defaultdict


def run(n, d):
    T = d * d + 2 * d * n - n * n
    L = d + n
    B = 3 * L + 3 * T // 2 + 6

    def closed(par, t, s):
        if par == 0:
            return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
        return n - T <= t <= d and 2 - d + n <= s <= T + L - 2

    def hspec(t):
        return (t % 2 == 0 and 2 <= t <= L - 2) or (t % 2 == 1 and n <= t <= d)

    def vspec(s):
        return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= L - 2))

    def is_arc(par, t, s):
        # (t, s, par) is a vertex of freeH, freeV, freeH + V or freeV + U
        if closed(par, t, s) and not closed(1 - par, t, s - 0) and False:
            return False
        # freeH at v: v - (0,1) outside, t in H spectrum
        if closed(par, t, s) and not closed(1 - par, t + d, s - (d - n)) and hspec(t):
            return True
        # freeV at v: v - (1,0) outside, s in V spectrum
        if closed(par, t, s) and not closed(1 - par, t - n, s - L) and vspec(s):
            return True
        # top: u = v - V has grades (t + T, s), freeH at u
        tu, su = t + T, s
        if closed(par, tu, su) and not closed(1 - par, tu + d, su - (d - n)) and hspec(tu):
            return True
        # right: u = v - U has grades (t, s - T), freeV at u
        tu, su = t, s - T
        if closed(par, tu, su) and not closed(1 - par, tu - n, su - L) and vspec(su):
            return True
        return False

    def strict(par, t, s):
        if par == 0:
            return d + n - 2 - T < t < 2 and 2 * n < s < T
        return d - T < t < n and L - 2 < s < T + 2 - d + n

    offs = [(dx, dy) for dx, dy in product((-1, 0, 1), repeat=2) if (dx, dy) != (0, 0)]
    block = [(dx, dy) for dx, dy in product((-1, 0, 1), repeat=2)]
    groups = {}
    count = defaultdict(int)
    for par in (0, 1):
        for t in range(-B, B + 1):
            if t % 2 != par:
                continue
            for s in range(-B, B + 1):
                if s % 2 != 0 or not strict(par, t, s):
                    continue
                for dx, dy in offs:
                    dt, ds = n * dx - d * dy, (d + n) * dx + (d - n) * dy
                    tw, sw = t + dt, s + ds
                    pw = par ^ ((dx + dy) % 2)
                    pat = []
                    if tw >= (2 if pw == 0 else n): pat.append('A')
                    if tw <= (L - 2 if pw == 0 else d) - T: pat.append('B')
                    if sw <= (2 * n if pw == 0 else L - 2): pat.append('C')
                    if sw >= T + (0 if pw == 0 else 2 - d + n): pat.append('D')
                    if not pat:
                        continue
                    key = ((dx, dy), tuple(pat), par)
                    good = set()
                    for ex, ey in block:
                        wt = t + n * ex - d * ey
                        ws = s + (d + n) * ex + (d - n) * ey
                        if is_arc(par ^ ((ex + ey) % 2), wt, ws):
                            good.add((ex, ey))
                    if key in groups:
                        groups[key] &= good
                    else:
                        groups[key] = good
                    count[key] += 1
    return groups, count


if __name__ == '__main__':
    for n, d in [(3, 7), (5, 9), (1, 5), (3, 11), (5, 11)]:
        groups, count = run(n, d)
        empty = {k: sorted(v) for k, v in groups.items() if not v}
        print(f'n={n} d={d} groups={len(groups)} empty={len(empty)}')
        for k in sorted(empty, key=str)[:6]:
            print('    empty', k, count[k])
