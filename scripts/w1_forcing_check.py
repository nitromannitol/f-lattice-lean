"""Task 60 numerics: W1Forced on the strict interior E° of a child (W1_CONSTRUCTOR §1-§6), from no seeds.

Model field G = standard(u) (Python permit_local), white = laplacian 0 with incomingNeg/incomingPos (Graph.lean).
Least fixed point of the forced pairs (c, p), p an input of c (p = incomingNeg c or incomingPos c):
  (c, p) is forced if some unit square Q ∋ c lies in E°, p ∉ Q, and every other corner c' of Q is black (laplacian -1) or a
  white with a forced pair (c', p') with p' ∈ Q.
Relaxation: pointers are not made consistent (Lean uses one global `inside`); a site counts as forced if it has some forced pair.
Reports, per word, the strict whites that are NOT forced (ideally none).
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
import importlib.util
spec = importlib.util.spec_from_file_location('cc', '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts/w1_collar_check.py')
_sv = sys.argv; sys.argv = [_sv[0], '2', '30']
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
sys.argv = _sv
from permit_local import standard, Frame, parents

def inn(x):
    return (x[0] - 1, x[1]) if (x[0] + x[1]) % 2 == 0 else (x[0], x[1] - 1)

def inp(x):
    return (x[0] + 1, x[1]) if (x[0] + x[1]) % 2 == 0 else (x[0], x[1] + 1)

def lap(G, x):
    return (G(inn(x)) - G(x)) + (G(inp(x)) - G(x))

def run(u):
    P = cc.params(u)
    G, _ = standard(tuple(u))
    M = 3 * P['d'] + 3
    E0 = set((x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.strict(P, (x, y)))
    white = {c: (lap(G, c) == 0) for c in E0}
    blacks = {c for c in E0 if lap(G, c) == -1}
    whites = [c for c in E0 if white[c]]
    # candidate squares for each white
    squares = {}
    for c in whites:
        sq = []
        for a in (c[0] - 1, c[0]):
            for b in (c[1] - 1, c[1]):
                corners = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if all(q in E0 for q in corners):
                    sq.append((a, b, corners))
        squares[c] = sq
    forced = {}  # c -> set of pointers
    changed = True
    while changed:
        changed = False
        for c in whites:
            for (a, b, corners) in squares[c]:
                for p in (inn(c), inp(c)):
                    if p in corners:
                        continue
                    ok = True
                    for q in corners:
                        if q == c:
                            continue
                        if q in blacks:
                            continue
                        if q not in whites:
                            ok = False; break
                        # white corner: needs a forced pointer inside the square
                        if not any(pp in corners for pp in forced.get(q, ())):
                            ok = False; break
                    if ok and p not in forced.get(c, set()):
                        forced.setdefault(c, set()).add(p)
                        changed = True
    unforced = [c for c in whites if c not in forced]
    return len(E0), len(whites), len(blacks), unforced

if __name__ == '__main__':
    for L_ in (1, 2, 3):
        for u in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in u) or all(x == 2 for x in u):
                continue
            nE, nW, nB, un = run(u)
            print(''.join(map(str, u)), 'E° sites', nE, 'whites', nW, 'blacks', nB, 'unforced whites', len(un), un[:3], flush=True)


def run_measure(u):
    """The stronger check (the hypotheses of Lean's forcing_of_measure): one pointer out(c) and a rank mu(c) per white c, with
    a square Q ∋ c in E°, out(c) ∉ Q, and every other white corner c' of Q with out(c') ∈ Q and mu(c') < mu(c)
    (or black). The pointer out(c) and the rank mu(c) are the earliest round and pointer of the least fixed point."""
    P = cc.params(u)
    G, _ = standard(tuple(u))
    M = 3 * P['d'] + 3
    E0 = set((x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.strict(P, (x, y)))
    whites = [c for c in E0 if lap(G, c) == 0]
    blacks = {c for c in E0 if lap(G, c) == -1}
    wset = set(whites)
    squares = {}
    for c in whites:
        sq = []
        for a in (c[0] - 1, c[0]):
            for b in (c[1] - 1, c[1]):
                corners = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if all(q in E0 for q in corners):
                    sq.append(corners)
        squares[c] = sq
    rnd = {}   # (c, p) -> round
    rounds = 0
    cur = 0
    while True:
        new = []
        for c in whites:
            for corners in squares[c]:
                for p in (inn(c), inp(c)):
                    if p in corners or (c, p) in rnd:
                        continue
                    ok = True
                    for q in corners:
                        if q == c or q in blacks:
                            continue
                        if q not in wset:
                            ok = False; break
                        if not any((q, pp) in rnd and rnd[(q, pp)] < cur + 1 and pp in corners for pp in (inn(q), inp(q))):
                            ok = False; break
                    if ok:
                        new.append((c, p))
        if not new:
            break
        cur += 1
        for pr in new:
            rnd[pr] = cur
    out = {}
    mu = {}
    for c in whites:
        cands = [(rnd[(c, p)], p) for p in (inn(c), inp(c)) if (c, p) in rnd]
        if not cands:
            return 'no forced pointer', c
        r, p = min(cands)
        out[c] = p
        mu[c] = r
    # verify the forcing_of_measure hypotheses
    for c in whites:
        good = False
        for corners in squares[c]:
            if out[c] in corners:
                continue
            ok = True
            for q in corners:
                if q == c or q in blacks:
                    continue
                if q not in wset or out[q] not in corners or not (mu[q] < mu[c]):
                    ok = False; break
            if ok:
                good = True; break
        if not good:
            return 'fails at', c
    return 'ok', len(whites)

if __name__ == '__main__' and len(sys.argv) > 0:
    print('--- measure form ---', flush=True)
    for L_ in (1, 2, 3):
        for u in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in u) or all(x == 2 for x in u):
                continue
            print(''.join(map(str, u)), run_measure(u), flush=True)
