# Numerical check of W1Forced at the pure-threes child 1/d, d = 2K+3 (task 72, W1 forcing base).
# Field: the archive doubled residual (forced/source, prove_rank.py definitions: shift U=(d,1), V=(1-d,d+1), aliases |i|<=2, |j|<=1,
# last native alias wins); laplacian = glap/2 in {0,-1}. Strict interior: the W1 grades with n=1 (T = d^2+2d-1). Forcing: the unit
# square rule of ForcedEdgeIn with R = StrictInterior and no seeds, to a fixpoint. Run: python3 w1_forced_numerics.py 0 4
# Result (K=0..4): every white of the strict interior is forced, no free white lies in it, forced arrows are W for x<=0 and E for x>=2.
#
# Numerics for W1Forced at the pure-threes child 1/d, d = 2K+3 (archive: forced/EXACT_FORCED_CLASSIFICATION...).
# Field: the archive's doubled residual (min over native aliases, last native alias wins), laplacian = glap/2 in {0,-1}.
import sys

def run(K):
    d = 2 * K + 3
    n = 1
    T = d * d + 2 * d * n - n * n
    aliases = [(i, j) for i in range(-2, 3) for j in (-1, 0, 1)]

    def native(X, Y):
        return ((2 - d <= X <= d and 0 <= Y <= d + 1 and 1 <= X + Y <= d + 2)
                or (X, Y) == (0, 0) or (X, Y) == (2, d + 1))

    def shift(X, Y, i, j):
        return (X + i * d + j * (1 - d), Y + i + j * (d + 1))

    def corr(a, b):
        return min(a - 1, 0) + (1 if (a, b) in ((0, 0), (2, d + 1)) else 0)

    incoherent = [0]

    def res(X, Y):
        out = None
        vals = set()
        for i, j in aliases:
            a, b = shift(X, Y, i, j)
            if native(a, b):
                v = (2 * corr(a, b) - 2 * d * i * j + 2 * d * j - i * i - 2 * i * j - 2 * i * Y + i
                     - 2 * j * j - 2 * j * X - 2 * j * Y + 2 * j)
                vals.add(v)
                out = v
        if len(vals) > 1:
            incoherent[0] += 1
        return 0 if out is None else out

    def glap(X, Y):
        if (X + Y) % 2 == 0:
            return res(X - 1, Y) + res(X + 1, Y) - 2 * res(X, Y)
        return -2 + res(X, Y - 1) + res(X, Y + 1) - 2 * res(X, Y)

    def lap(X, Y):
        g = glap(X, Y)
        assert g in (0, -2), ('doubled laplacian not binary', X, Y, g)
        return g // 2

    def free(X, Y):
        H = (Y == 0 and 1 <= X <= d)
        V = ((X, Y) == (0, 0) or (X + Y == 1 and 1 <= Y < d) or (X == 2 - d and Y == d))
        return H or V

    def inner(X, Y):
        t = n * X - d * Y
        s = (d + n) * X + (d - n) * Y
        even = (X + Y) % 2 == 0
        a = 2 if even else n
        b = d + n - 2 if even else d
        c = 0 if even else 2 - d + n
        h = 2 * n if even else d + n - 2
        return (b - T < t < a) and (h < s < T + c)

    B = 2 * T + 2
    SI = set()
    for Y in range(-B, B + 1):
        for X in range(-B, B + 1):
            if inner(X, Y):
                SI.add((X, Y))
    # the strict interior must lie well inside the box
    assert all(abs(x) < B - 2 and abs(y) < B - 2 for (x, y) in SI), 'box too small'
    lapv = {c: lap(*c) for c in SI}
    whites = {c for c in SI if lapv[c] == 0}
    freeSI = {c for c in SI if free(*c)}
    # unit-square closure restricted to squares inside SI (ForcedEdgeIn with R = StrictInterior, no seeds)
    forced = {}  # c -> set of targets

    def inc(c):
        x, y = c
        if (x + y) % 2 == 0:
            return (x - 1, y), (x + 1, y)
        return (x, y - 1), (x, y + 1)

    changed = True
    rounds = 0
    while changed:
        changed = False
        rounds += 1
        for (x, y) in SI:
            for a, b in ((x, y), (x - 1, y), (x, y - 1), (x - 1, y - 1)):
                Q = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if not all(q in SI for q in Q):
                    continue
                Qs = set(Q)
                for c in Q:
                    if c not in whites or c in forced:
                        continue
                    others = [q for q in Q if q != c]
                    ok = all(lapv[q] == -1 or (lapv[q] == 0 and any(t in Qs for t in forced.get(q, ())))
                             for q in others)
                    if not ok:
                        continue
                    for o in inc(c):
                        if o not in Qs:
                            forced.setdefault(c, set()).add(o)
                            changed = True
                            break
    unforced = sorted(whites - set(forced))
    # arrows: W (incomingNeg) for x <= 0, E for x >= 2 (archive); report the direction counts
    dirs = {}
    for c, ts in forced.items():
        x, y = c
        for t in ts:
            key = ('W' if t[0] < c[0] else 'E' if t[0] > c[0] else 'V') if (x + y) % 2 == 0 else ('S' if t[1] < c[1] else 'N')
            dirs[(c[0] <= 0, c[0] >= 2, key)] = dirs.get((c[0] <= 0, c[0] >= 2, key), 0) + 1
    print('K=%d d=%d T=%d strictInterior=%d whites=%d free-in-SI=%d forced=%d unforced=%d rounds=%d incoherent=%d'
          % (K, d, T, len(SI), len(whites), len(freeSI), len(forced), len(unforced), rounds, incoherent[0]))
    if unforced:
        print('  unforced sample:', unforced[:12])
    print('  arrows (x<=0, x>=2, dir):', dict(sorted(dirs.items())))

for K in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    run(K)
