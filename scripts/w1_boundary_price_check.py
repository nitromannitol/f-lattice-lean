"""Task 69 numerics: the boundary bound P <= c0 on dE and the arc facts, on the actual standard fields (proper words).

P(z) = F(z) - F(z - v) - eps (N z1 - D z2), v = eps (N - D, N + D), c0 = (Tp - eps (N + D)) / 2 (ChildFrame.cutPrice).
Checks, per proper word (length <= 3 by default):
  * c0 - 1 <= P <= c0 on the closed polygon E (the price range, the claim being proved in Lean);
  * on the boundary dE: P <= c0 and P >= c0 - 1;
  * on the pure bottom arc: F(z) = 0 (zero strip), F(z - v) = h0(z - v), and h0(z) >= 0 (the three arc facts of task 69 (i));
  * on the H cut freeH (bottom boundary with t in the H spectrum): h0 >= 0.
"""
import itertools
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import importlib.util  # noqa: E402
import permit_local as pl  # noqa: E402

_sv = sys.argv
sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', str(Path(__file__).parent / 'w1_collar_check.py'))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)
sys.argv = _sv


def h0(x):
    return (x[0] ** 2 + 2 * x[0] * x[1] - x[1] ** 2 - 2 * x[1] - ((x[0] + x[1]) % 2)) // 4


def closed_E(P, z):
    """The closed polygon E (ChildFrame.closedPolygon): the parity rectangle in (t, s)."""
    n, d, L, T = P['n'], P['d'], P['L'], P['T']
    t = n * z[0] - d * z[1]
    s = L * z[0] + (d - n) * z[1]
    if (z[0] + z[1]) % 2 == 0:
        return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
    return n - T <= t <= d and 2 - d + n <= s <= T + L - 2


def run(u):
    P = cc.params(tuple(u))
    G, _ = pl.standard(tuple(u))
    eps, N, D, n, d, T = P['eps'], P['N'], P['D'], P['n'], P['d'], P['T']
    v = (eps * (N - D), eps * (N + D))
    c0 = (P['Tp'] - eps * (N + D)) // 2
    M = 3 * (d + n) + 4

    def price(z):
        return G(z) - G((z[0] - v[0], z[1] - v[1])) - eps * (N * z[0] - D * z[1])

    stats = Counter()
    Ecl = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if closed_E(P, (x, y))]
    Eset = set(Ecl)
    for z in Ecl:
        p = price(z)
        stats['E_sites'] += 1
        if not (c0 - 1 <= p <= c0):
            stats['E_range_violation'] += 1
        nbrs = [(z[0] + 1, z[1]), (z[0] - 1, z[1]), (z[0], z[1] + 1), (z[0], z[1] - 1)]
        out = {'E': (z[0], z[1] - 1) not in Eset, 'W': (z[0] - 1, z[1]) not in Eset,
               'Ea': (z[0] + 1, z[1]) not in Eset, 'N': (z[0], z[1] + 1) not in Eset}
        if not any(out.values()):
            continue
        stats['boundary_sites'] += 1
        if p > c0:
            stats['boundary_P_above_c0'] += 1
        if p < c0 - 1:
            stats['boundary_P_below_c0m1'] += 1
        pure_bottom = out['E'] and not out['W'] and not out['Ea']
        if pure_bottom:
            stats['pure_bottom'] += 1
            if G(z) != 0:
                stats['bottom_F_not_zero'] += 1
            if G((z[0] - v[0], z[1] - v[1])) != h0((z[0] - v[0], z[1] - v[1])):
                stats['bottom_source_not_h0'] += 1
            if h0(z) < 0:
                stats['bottom_h0_negative'] += 1
    return stats


if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    from exact_quotient import words  # noqa: E402
    ws = [w for w in words(maxlen)]
    tot = Counter()
    for w in ws:
        tot.update(run(w))
    print('words', len(ws), dict(tot), flush=True)
