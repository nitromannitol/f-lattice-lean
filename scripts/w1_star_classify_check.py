"""Task 69 numerics: the star classification (StrongUnitPrice.StarClassified) on the centres of E.

For each proper word, each centre c in the closed polygon E and each site x of its full star (c, incomingNeg c, incomingPos c), x must be
  (a) in E, or
  (b) an H-band site: even s in [2n, T], odd s in [L, T - c], or
  (c) in the h0 strip window s in [3 - 2d, 2L - 1] (then F = h0 at x and at x - v, the V-source condition, by the strip).
Deck translates (U, V shift P by -k and 0) make this the full classification of the stars (every centre is a deck translate of a centre of E).
Reports the failures.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import importlib.util  # noqa: E402
_sv = sys.argv
sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', str(Path(__file__).parent / 'w1_collar_check.py'))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)
sys.argv = _sv
from w1_boundary_price_check import closed_E  # noqa: E402
from exact_quotient import words  # noqa: E402


def inn(z):
    return (z[0] - 1, z[1]) if (z[0] + z[1]) % 2 == 0 else (z[0], z[1] - 1)


def inp(z):
    return (z[0] + 1, z[1]) if (z[0] + z[1]) % 2 == 0 else (z[0], z[1] + 1)


def run(u):
    P = cc.params(tuple(u))
    n, d, L, T = P['n'], P['d'], P['L'], P['T']
    stats = Counter()
    M = 3 * (d + n) + 4
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            c = (x, y)
            if not closed_E(P, c):
                continue
            stats['centres'] += 1
            for site in (c, inn(c), inp(c)):
                t = n * site[0] - d * site[1]
                s = L * site[0] + (d - n) * site[1]
                if closed_E(P, site):
                    stats['in_E'] += 1
                    continue
                even = (site[0] + site[1]) % 2 == 0
                hband = (2 * n <= s <= T) if even else (L <= s <= T - (d - n))
                if hband:
                    stats['H_band'] += 1
                    continue
                if 3 - 2 * d <= s <= 2 * L - 1:
                    stats['h0_window'] += 1
                    continue
                stats['FAIL'] += 1
                if stats['FAIL'] <= 3:
                    stats.setdefault('examples', [])
                    stats['examples'] = stats['examples']  # keep count only
    return stats


if __name__ == '__main__':
    tot = Counter()
    for w in words(3):
        tot.update(run(w))
    print('words', len(list(words(3))), dict(tot), flush=True)
