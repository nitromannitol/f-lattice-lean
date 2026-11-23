"""Task 61 numerics: the §5 tie claims in the model.

Sheets of the even child u (child n/d, odd parent N/D, even parent nq/dq, eps, W): Fp(x) = Fq(Zx) + h0(x), Fq = standard(swap(oddBirthPrefix
u)); A(z) = Fp(z - lv), C(z) = Fp(z - lv - e) + a(z - lv) + ce, lv = (1-W)(dq,nq), e = Vq + eps(dq,nq), a(x) = nq x1 - dq x2,
ce = (Tq - dq - nq)/2 + 2W. F = standard(u) = min(A, C) on E (checked). Ψ = C - A.
Checks on E° (strict): (1) F = min(A,C) on E; (2) at a white c of F with Ψ(c) = 0 (a tie): do both inputs of c have Ψ = 0?
(3) Ψ unit increments along edges (|ΔΨ| ≤ 1).
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
import importlib.util
_sv = sys.argv; sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts/w1_collar_check.py')
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
sys.argv = _sv
from permit_local import standard, Frame, h0, parents, odd_birth_prefix, swap
from w1_forcing_check import inn, inp, lap

Z = lambda x: (-x[1], x[0] - 1)

def sheets(u):
    (N, D), (nq, dq) = parents(u)
    fr = Frame(u)
    eps = fr.eps
    W = (1 + eps) // 2
    Fq, _ = standard(tuple(swap(odd_birth_prefix(u))))
    Fp = lambda x: Fq(Z(x)) + h0(*x)
    lv = ((1 - W) * dq, (1 - W) * nq)
    Vq = (nq - dq, dq + nq)
    e = (Vq[0] + eps * dq, Vq[1] + eps * nq)
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    A = lambda z: Fp((z[0] - lv[0], z[1] - lv[1]))
    C = lambda z: Fp((z[0] - lv[0] - e[0], z[1] - lv[1] - e[1])) + nq * (z[0] - lv[0]) - dq * (z[1] - lv[1]) + ce
    return A, C

def test(u):
    P = cc.params(u)
    G, _ = standard(tuple(u))
    A, C = sheets(u)
    M = 3 * P['d'] + 3
    E = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.in_E(P, (x, y)) if False] if False else None
    fr = Frame(list(u))
    E = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if fr.inE((x, y))]
    Eo = set(z for z in E if cc.strict(P, z))
    min_bad = sum(1 for z in E if G(z) != min(A(z), C(z)))
    psi = lambda z: C(z) - A(z)
    ties = [c for c in Eo if lap(G, c) == 0 and psi(c) == 0]
    tie_bad = []
    for c in ties:
        if not (psi(inn(c)) == 0 and psi(inp(c)) == 0):
            tie_bad.append(c)
    unit_bad = 0
    for c in Eo:
        for i in (inn(c), inp(c)):
            if abs(psi(i) - psi(c)) > 1:
                unit_bad += 1
    return dict(E=len(E), min_bad=min_bad, ties=len(ties), tie_bad=len(tie_bad), tie_bad_ex=tie_bad[:2], unit_bad=unit_bad)

if __name__ == '__main__':
    for L_ in (1, 2, 3):
        for u in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in u) or all(x == 2 for x in u):
                continue
            print(''.join(map(str, u)), test(u), flush=True)
