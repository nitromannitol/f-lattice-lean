"""Task 70 (arc profile) numerics: which strip each sheet argument falls in, per boundary arc (proper words, length <= 3).

Parent (odd N/D, even sibling nq/dq), conjugate field G = standardField(conjWord): its child (n_c, d_c) = (D - N, D + N).
Fp(x) = quarterTurnField G x = G(Zx) - h0(Zx), Zx = (-x2, x1 - 1). Zero band of G at Zx: t_c(Zx) = L_p - s_p(x) in [1 - d_c, n_c + 2 d_c - 1],
i.e. s_p(x) in [1 - 2D, 2(D + N) - 1]: then Fp(x) = -h0(Zx). h0 band: s_c(Zx) = 2 t_p(x) - 2N in [1 - 2 d_c, 2(d_c + n_c) - 1],
i.e. t_p(x) in [1 - D, N + 2D - 1]: then Fp(x) = 0.
Sheet arguments: A(z) = Fp(z - lv), C(z) = Fp(z - lv - e) + ..., lv = (1 - W) (dq, nq), e = (nq - dq, nq + dq) + eps (dq, nq).
For the representative y of z - v in E (z - v + kU), the same two arguments at y.
"""
from collections import Counter
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import importlib.util
_sv = sys.argv
sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', str(Path(__file__).parent / 'w1_collar_check.py'))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)
sys.argv = _sv
from w1_boundary_price_check import closed_E  # noqa: E402
from exact_quotient import words  # noqa: E402


def tp(P, x):
    return P['N'] * x[0] - P['D'] * x[1]


def sp(P, x):
    return (P['D'] + P['N']) * x[0] + (P['D'] - P['N']) * x[1]


def band(P, x):
    s = sp(P, x)
    t = tp(P, x)
    z = 1 - 2 * P['D'] <= s <= 2 * (P['D'] + P['N']) - 1
    h = 1 - P['D'] <= t <= P['N'] + 2 * P['D'] - 1
    if z and h:
        return 'both'
    if z:
        return 'zero'
    if h:
        return 'h0'
    return 'none'


def arcs(P, z, closed):
    x, y = z
    out = {'S': not closed(P, (x, y - 1)), 'N': not closed(P, (x, y + 1)),
           'W': not closed(P, (x - 1, y)), 'E': not closed(P, (x + 1, y))}
    if not any(out.values()):
        return None
    if out['S'] and not out['W'] and not out['E']:
        return 'bottom'
    if out['N'] and not out['W'] and not out['E']:
        return 'top'
    if out['W']:
        return 'left'
    if out['E']:
        return 'right'
    return 'other'


def run(u, stats):
    P = cc.params(tuple(u))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    lv = ((1 - W) * dq, (1 - W) * nq)
    e = (nq - dq + eps * dq, nq + dq + eps * nq)
    v = (eps * (N - D), eps * (N + D))
    M = 3 * (P['d'] + P['n']) + 4
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            z = (x, y)
            if not closed_E(P, z):
                continue
            arc = arcs(P, z, closed_E)
            if arc is None:
                continue
            xa = (z[0] - lv[0], z[1] - lv[1])
            xc = (xa[0] - e[0], xa[1] - e[1])
            stats[(arc, 'A', band(P, xa))] += 1
            stats[(arc, 'C', band(P, xc))] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st):
        print(k, st[k], flush=True)
