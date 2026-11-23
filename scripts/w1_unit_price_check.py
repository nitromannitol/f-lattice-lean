"""Task 69 numerics: HasUnitPrice and NoPriceSaddle of the primitive price on the actual standard fields (proper words, length <= 3).

For every centre c in the closed polygon E and each input i of c: |P(i) - P(c)| <= 1 (HasUnitPrice on those edges), and the star of c has no
opposite unit increments (NoPriceSaddle). By the deck (P(z + U) = P z - 1, P(z + V) = P z) the stars of E cover all stars up to translation.
P(z) = F(z) - F(z - v) - eps (N z1 - D z2), v = eps (N - D, N + D).
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import permit_local as pl  # noqa: E402
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
    G, _ = pl.standard(tuple(u))
    eps, N, D, n, d = P['eps'], P['N'], P['D'], P['n'], P['d']
    v = (eps * (N - D), eps * (N + D))

    def price(z):
        return G(z) - G((z[0] - v[0], z[1] - v[1])) - eps * (N * z[0] - D * z[1])

    stats = Counter()
    M = 3 * (d + n) + 4
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            c = (x, y)
            if not closed_E(P, c):
                continue
            pc = price(c)
            dn = price(inn(c)) - pc
            dp = price(inp(c)) - pc
            for dd in (dn, dp):
                stats['increments'] += 1
                if not (-1 <= dd <= 1):
                    stats['unit_violation'] += 1
            if (dn == -1 and dp == 1) or (dn == 1 and dp == -1):
                stats['saddle'] += 1
    return stats


if __name__ == '__main__':
    tot = Counter()
    for w in words(3):
        tot.update(run(w))
    print('words', len(list(words(3))), dict(tot), flush=True)
