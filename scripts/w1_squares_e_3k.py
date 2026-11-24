"""Unit square clauses (SquareClauseSat, SquareClauses.lean) for the selection of e(-1,eta) (task 118, W1 base).
SquareClauseSat F sel a b  :=  not (every corner c of the square {(a,b),(a+1,b),(a,b+1),(a+1,b+1)} is keptInside), where
keptInside c S  :=  (if laplacian c = -1 then incomingNeg c in S or incomingPos c in S else sel c in S).
Conventions as in w1_signed_e_3k.py: even c has incomingNeg/Pos = c -/+ (1,0), odd c has c -/+ (0,1); the selection of a white
is its single retained input. The policy is deck-equivariant: sel(c) = sel(r) + lam where c = r + lam, lam = aU + bV in the deck
lattice (U = (d,1), V = (1-d,1+d)) and r native. Every square class has a representative with lower-left corner native, so
the squares with native lower-left corners (a, b) cover all clauses."""
import sys, importlib.util
sys.path.insert(0, 'scripts')
spec = importlib.util.spec_from_file_location('se', 'scripts/w1_signed_e_3k.py')
SE = importlib.util.module_from_spec(spec); spec.loader.exec_module(SE)

def even(c): return (c[0] + c[1]) % 2 == 0

def run(k, etas=(1, -1)):
    E = SE.E(k); d = E.d
    native = set(E.native)
    U = (d, 1); V = (1 - d, 1 + d)
    def rep(c):
        for a in range(-6, 7):
            for b in range(-6, 7):
                lam = (a * U[0] + b * V[0], a * U[1] + b * V[1])
                r = (c[0] - lam[0], c[1] - lam[1])
                if r in native: return r, lam
        raise ValueError(('no native rep', c))
    def lap(c):
        r, _ = rep(c); return E.P0.lap(r)
    def sel(eta, c):
        r, lam = rep(c)
        out = E.select(eta, r)
        return {(p[0] + lam[0], p[1] + lam[1]) for p in out}
    def inc(c):
        x, y = c
        return ((x - 1, y), (x + 1, y)) if even(c) else ((x, y - 1), (x, y + 1))
    res = {}
    for eta in etas:
        viol = []
        for (a, b) in native:
            S = {(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)}
            def kept(c):
                if lap(c) == -1:
                    return any(q in S for q in inc(c))
                s = sel(eta, c)
                return all(q in S for q in s) and len(s) > 0
            if all(kept(c) for c in S):
                viol.append((a, b))
        res[eta] = viol
    return res

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or list(range(0, 4))
    for k in ks:
        r = run(k)
        for eta in (1, -1):
            v = r[eta]
            print('k=%d eta=%+d: squares with all corners kept inside: %d %s' % (k, eta, len(v), v[:5]), flush=True)
