"""Task 69 numerics: the values of P on the four arcs of the boundary of E (actual standard fields, proper words, length <= 3).

Arcs (w1 cover): pure bottom (outward south, no west/east), pure top (outward north, no west/east), left V (outward west), right V (outward east).
For each site record P - c0 and the arc; report the value histogram per arc, and the exceptional sites (value outside {c0-1, c0}).
"""
import sys
from collections import Counter, defaultdict
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


def run(u, hist, exc):
    P = cc.params(tuple(u))
    G, _ = pl.standard(tuple(u))
    eps, N, D, n, d = P['eps'], P['N'], P['D'], P['n'], P['d']
    c0 = (P['Tp'] - eps * (N + D)) // 2
    v = (eps * (N - D), eps * (N + D))

    def price(z):
        return G(z) - G((z[0] - v[0], z[1] - v[1])) - eps * (N * z[0] - D * z[1])

    M = 3 * (d + n) + 4
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            z = (x, y)
            if not closed_E(P, z):
                continue
            out = {'S': not closed_E(P, (x, y - 1)), 'N': not closed_E(P, (x, y + 1)),
                   'W': not closed_E(P, (x - 1, y)), 'E': not closed_E(P, (x + 1, y))}
            if not any(out.values()):
                continue
            if out['S'] and not out['W'] and not out['E']:
                arc = 'pure_bottom'
            elif out['N'] and not out['W'] and not out['E']:
                arc = 'pure_top'
            elif out['W']:
                arc = 'left_V'
            elif out['E']:
                arc = 'right_V'
            else:
                arc = 'other'
            val = price(z) - c0
            hist[(arc, val)] += 1
            if val not in (0, -1):
                exc[arc].append((tuple(u), z, val))


if __name__ == '__main__':
    hist = Counter()
    exc = defaultdict(list)
    for w in words(3):
        run(w, hist, exc)
    for k in sorted(hist):
        print(k, hist[k])
    for arc in exc:
        print('exceptions', arc, len(exc[arc]), exc[arc][:4])
