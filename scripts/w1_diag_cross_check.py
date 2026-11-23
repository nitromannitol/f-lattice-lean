"""Task 63 numerics: cross-phase corner pairs in unit squares of E° (words of length <= 3).
A diagonal pair with Ψ = +1 and Ψ = −1 is possible only with both other corners tie (Ψ = 0); adjacent cross pairs never occur.
Output: counts of diagonal cross pairs, adjacent cross pairs, and diagonal cross pairs whose other corners are not ties (expected 0)."""
import sys, itertools
sys.argv = ['x']
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
import w1_phase_check as pc
from w1_tie_check import sheets
from w1_forcing_check import lap
from permit_local import standard
import w1_collar_check as cc
# diagonal cross-phase pairs in unit squares of E0 (strict corners), and what the other two corners are
tot = {'diag_cross': 0, 'adj_cross': 0, 'diag_cross_other_not_ties': 0}
for L_ in (1, 2, 3):
    for u in itertools.product((1, 2, 3), repeat=L_):
        if all(x == 3 for x in u) or all(x == 2 for x in u):
            continue
        P = cc.params(u); G, _ = standard(tuple(u)); A, C = sheets(u)
        psi = lambda z: C(z) - A(z)
        M = 3 * P['d'] + 3
        E0 = set((x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.strict(P, (x, y)))
        for a in range(-M, M):
            for b in range(-M, M):
                cs = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if not all(q in E0 for q in cs):
                    continue
                for (p, q), (r, s) in [((cs[0], cs[3]), (cs[1], cs[2]))]:
                    vp, vq = psi(p), psi(q)
                    if vp != 0 and vq != 0 and (vp > 0) != (vq > 0):
                        tot['diag_cross'] += 1
                        others = [psi(r), psi(s)]
                        if any(v != 0 for v in others):
                            tot['diag_cross_other_not_ties'] += 1
                for p, q in [(cs[0], cs[1]), (cs[0], cs[2]), (cs[1], cs[3]), (cs[2], cs[3])]:
                    vp, vq = psi(p), psi(q)
                    if vp != 0 and vq != 0 and (vp > 0) != (vq > 0):
                        tot['adj_cross'] += 1
    print(''.join(map(str, u)), tot, flush=True)
print('final', tot)
