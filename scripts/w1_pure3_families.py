"""Family decomposition of the native domain and the piecewise Q_minus rank (task 118, W1 base, step (ii)).
Checks that the piecewise formula equals the replay's rank (w1_pure3_rank_gate.py) on every native point, for odd d = 3..15,
and that the families partition the native domain."""
import importlib.util
from collections import Counter
spec = importlib.util.spec_from_file_location('g', 'scripts/w1_pure3_rank_gate.py')
g = importlib.util.module_from_spec(spec); spec.loader.exec_module(g)

def valMinus(d, x, y):
    p = (x + y) % 2
    if y == 0 and 1 <= x <= d: return 2 * x + p
    if (x == 0 and y == 0) or (x + y == 1 and 1 <= y < d) or (x == 2 - d and y == d): return -2 * y - p
    if x + y == d + 1 and x >= 1: return 2 * x
    if x <= 0: return 2 * x - 4 + p
    return 4 * d - 4 - 2 * x + p

def isfree(d, x, y):
    return (y == 0 and 1 <= x <= d) or (x == 0 and y == 0) or (x + y == 1 and 1 <= y < d) or (x == 2 - d and y == d)

def family(d, x, y):
    if isfree(d, x, y): return 'F0 free'
    if (x, y) == (2, d + 1): return 'F3 corner'
    if y == d + 1: return 'F2 top'
    if (x, y) == (d, 1): return 'F5 (d,1)'
    if x + y == d + 2: return 'F4 anti-diagonal'
    return 'F1 interior'

def rankQ(d, x, y):
    f = family(d, x, y)
    if f == 'F0 free' or f == 'F1 interior': return valMinus(d, x, y)
    if f == 'F2 top': return valMinus(d, x + d - 1, 0) - 2 * (d + 1)
    if f == 'F3 corner': return valMinus(d, 2 - d, d) + 2 * d
    if f == 'F5 (d,1)': return valMinus(d, 0, 0) + 2 * d
    return valMinus(d, x - d, y - 1) + 2 * d

if __name__ == '__main__':
    for d in range(3, 16, 2):
        F = g.make(d)
        pts = {(X, Y) for X in range(2 - d, d + 1) for Y in range(0, d + 2) if F['native'](X, Y)} | {(0, 0), (2, d + 1)}
        mism = [p for p in pts if rankQ(d, *p) != F['rank'](*p)]
        fam = Counter(family(d, *p) for p in pts)
        print('d=%d points %d mismatches %d' % (d, len(pts), len(mism)), dict(fam), mism[:3])
