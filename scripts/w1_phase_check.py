"""Task 62 numerics: the phase-exit properties of §5-§6 for unit squares in E°.

psi = Ψ = C − A (the sheets of w1_tie_check). For each white c of E° (F = standard(u)) ask whether some unit square Q ∋ c with corners in
E° has the phase property:
  (tie)   psi c = 0  : every other white corner c' of Q has psi c' = 0 or psi c' ≠ 0 (tie → strict is allowed);
  (strict) psi c ≠ 0 : every other white corner c' of Q has psi c' ≠ 0 and sign(psi c') = sign(psi c) (no strict→tie, no cross-phase).
Reports the whites with no such square (ideally none)."""
import itertools, sys
sys.path.insert(0, 'scripts')
from w1_tie_check import sheets
from w1_forcing_check import inn, inp, lap
import importlib.util
_sv = sys.argv; sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', 'scripts/w1_collar_check.py')
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
sys.argv = _sv
from permit_local import standard, Frame

def run(u):
    P = cc.params(u)
    G, _ = standard(tuple(u))
    A, C = sheets(u)
    psi = lambda z: C(z) - A(z)
    E0 = set((x, y) for x in range(-(3 * P['d'] + 3), 3 * P['d'] + 4) for y in range(-(3 * P['d'] + 3), 3 * P['d'] + 4) if cc.strict(P, (x, y)))
    whites = [c for c in E0 if lap(G, c) == 0]
    wset = set(whites)
    bad_tie, bad_strict, tot = [], [], 0
    for c in whites:
        tot += 1
        ok = False
        for a in (c[0] - 1, c[0]):
            for b in (c[1] - 1, c[1]):
                corners = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if not all(q in E0 for q in corners):
                    continue
                good = True
                for q in corners:
                    if q == c or q not in wset:
                        continue
                    if psi(c) == 0:
                        pass  # tie: any white corner allowed (tie->tie or tie->strict)
                    else:
                        if psi(q) == 0 or (psi(q) > 0) != (psi(c) > 0):
                            good = False; break
                if good:
                    ok = True; break
            if ok:
                break
        if not ok:
            (bad_tie if psi(c) == 0 else bad_strict).append(c)
    return tot, len(bad_tie), len(bad_strict), bad_strict[:2]

if __name__ == '__main__':
    for L_ in (1, 2, 3):
        for u in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in u) or all(x == 2 for x in u):
                continue
            print(''.join(map(str, u)), 'whites', run(u), flush=True)


def run_phase_lex(u):
    """The repaired order: ties first (leading component 1_{Ψ≠0}), then the fixed-point round. A unit square of c is admissible when its
    other white corners are ties if c is a tie, and ties or of the sign of Ψ(c) if c is strict. Pointers as in run_measure: the least
    fixed point over admissible squares; every white must be forced, and the lexicographic decrease holds by construction."""
    P = cc.params(u)
    G, _ = standard(tuple(u))
    A, C = sheets(u)
    psi = lambda z: C(z) - A(z)
    M = 3 * P['d'] + 3
    E0 = set((x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.strict(P, (x, y)))
    whites = [c for c in E0 if lap(G, c) == 0]
    wset = set(whites)
    blacks = {c for c in E0 if lap(G, c) == -1}
    squares = {}
    for c in whites:
        sq = []
        for a in (c[0] - 1, c[0]):
            for b in (c[1] - 1, c[1]):
                corners = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if not all(q in E0 for q in corners):
                    continue
                ok = True
                for q in corners:
                    if q == c or q not in wset:
                        continue
                    if psi(c) == 0:
                        if psi(q) != 0:
                            ok = False; break
                    else:
                        if not (psi(q) == 0 or (psi(q) > 0) == (psi(c) > 0)):
                            ok = False; break
                if ok:
                    sq.append(corners)
        squares[c] = sq
    forced = {}   # white c -> (round, pointer)
    rnd = 0
    while True:
        new = {}
        for c in whites:
            if c in forced:
                continue
            for corners in squares[c]:
                ok = True
                for q in corners:
                    if q == c or q in blacks:
                        continue
                    if q not in forced or forced[q][0] >= rnd + 1:
                        ok = False; break
                    if forced[q][1] not in corners:
                        ok = False; break
                if ok:
                    for p in (inn(c), inp(c)):
                        if p not in corners:
                            new[c] = (rnd + 1, p)
                            break
                    if c in new:
                        break
        if not new:
            break
        forced.update(new)
        rnd += 1
    unforced = [c for c in whites if c not in forced]
    return len(whites), len(unforced), unforced[:2]
