"""Task 71 numerics: the sheet formulas on E and the binding sheet on each arc (proper words, length <= 3).

Conjugate field G = standard(conjWord(w)); Fp(x) = G(Zx) - h0(Zx), Zx = (-x2, x1 - 1) (quarterTurn_eq_sub).
A(z) = Fp(z - lv), C(z) = Fp(z - lv - e) + aq.(z - lv) + c_e, with lv = (1 - W)(dq, nq), e = (nq - dq, nq + dq) + eps (dq, nq),
aq = (nq, -dq), c_e = (T_q - dq - nq)/2 + 2W, T_q = dq^2 + 2 dq nq - nq^2.
Checks: F(z) = min(A(z), C(z)) on E; and which sheet is the minimum on each boundary arc.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import permit_local as pl  # noqa: E402
import upper_attainment_check as uac  # noqa: E402
import importlib.util  # noqa: E402
_sv = sys.argv
sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', str(Path(__file__).parent / 'w1_collar_check.py'))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)
sys.argv = _sv
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_arc_band_check import arcs  # noqa: E402
from exact_quotient import words  # noqa: E402


def h0(x):
    return (x[0] ** 2 + 2 * x[0] * x[1] - x[1] ** 2 - 2 * x[1] - ((x[0] + x[1]) % 2)) // 4


def run(u, st):
    P = cc.params(tuple(u))
    Fch, _ = pl.standard(tuple(u))
    G, _ = pl.standard(tuple(uac.conjWord(list(u))))
    eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    lv = ((1 - W) * dq, (1 - W) * nq)
    e = (nq - dq + eps * dq, nq + dq + eps * nq)

    def Fp(x):
        zx = (-x[1], x[0] - 1)
        return G(zx) - h0(zx)

    def A(z):
        return Fp((z[0] - lv[0], z[1] - lv[1]))

    def C(z):
        x = (z[0] - lv[0] - e[0], z[1] - lv[1] - e[1])
        return Fp(x) + nq * (z[0] - lv[0]) - dq * (z[1] - lv[1]) + ce

    M = 3 * (P['d'] + P['n']) + 4
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            z = (x, y)
            if not closed_E(P, z):
                continue
            st['E_sites'] += 1
            if Fch(z) != min(A(z), C(z)):
                st['F_ne_min'] += 1
            arc = arcs(P, z, closed_E)
            if arc is None:
                continue
            a, c = A(z), C(z)
            which = 'A' if a < c else ('C' if c < a else 'tie')
            st[(arc, which)] += 1


if __name__ == '__main__':
    st = Counter()
    for w in words(3):
        run(w, st)
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
