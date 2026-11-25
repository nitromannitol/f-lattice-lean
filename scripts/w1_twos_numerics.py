# Numerics for W1Forced at the twos children (the child of 2^(k+1) is (2k+3)/(2k+5), a = 2k+4), task 72 (lead item 2).
# Checks: the closed form of the strict interior; the native black/white rule (laplacian_twos_native, with the quarter turn
# rot(u) = (2a-u_2, u_1+1) and the ladder predicates); the unit-square closure inside the strict interior; the archive's
# four forced classes L/U/E/W in the plane coordinates (x, y) (pure2_initialization/UNIFORM_DOUBLED_LADDER_BULK_DIRECTIONS.md)
# with their grades and witness squares. Run: python3 w1_twos_numerics.py
import sys
# Numerics for W1Forced at the twos child (2k+3)/(2k+5), i.e. a = 2k+4, n = a-1, d = a+1 (word 2^(k+1)).

def ev(p): return (p[0] + p[1]) % 2 == 0

def NativeT(a, x, y):
    A = (-1 <= x <= a+1 and 1 <= y+1 <= 3*a-1 and -1 <= y+1-x <= 2*a+1
         and not ((x == -1 and y+1 <= a+1) or (x == a+1 and 2*a-1 <= y+1)))
    return A or (x == -1 and y+1 == 2*a+1) or (x == a+1 and y+1 == a-1)

def rot(a, p): return (2*a - p[1], p[0] + 1)

def LadderOddLowerBoundary(den, p):
    x, y = p
    return ((x + y == 1 and 2 - den <= x <= -1) or (y == 0 and 1 <= x <= den-1) or (y == 1 and den <= x <= 2*den))

def reflectLadderOdd(den, p): return (den+2 - p[0], den+2 - p[1])

def LadderOddEvenBlack(den, p):
    x, y = p
    return ((x == 1 and 1 <= y <= den-1) or (x == den+1 and 3 <= y <= den+1) or (x+y == den+2 and 2 <= y <= den))

def LadderOddOddWhite(den, p):
    return (LadderOddLowerBoundary(den, p) or LadderOddLowerBoundary(den, reflectLadderOdd(den, p))
            or (p[0]+p[1] == den+1 and 1 <= p[1] <= den-1) or (p[0]+p[1] == den+3 and 3 <= p[1] <= den+1)
            or (p[0] == 0 and p[1] == 1) or (p[0] == den+2 and p[1] == den+1))

def lap_native(a, u):
    """The native twos Laplacian (laplacian_twos_native): -1 black, 0 white."""
    q = rot(a, u)
    if ev(q):
        return -1 if LadderOddEvenBlack(a, q) else 0
    return 0 if LadderOddOddWhite(a, q) else -1

def si_points(n, d):
    T = d*d + 2*d*n - n*n
    B = 2*T + 2
    out = []
    for Y in range(-B, B+1):
        for X in range(-B, B+1):
            t = n*X - d*Y; s = (d+n)*X + (d-n)*Y
            if ev((X, Y)):
                b = d+n-2; a_ = 2; c = 0; h = 2*n
            else:
                b = d; a_ = n; c = 2-d+n; h = d+n-2
            if (b - T < t < a_) and (h < s < T + c):
                out.append((X, Y))
    return out, T

def closure(SI, lap):
    whites = {c for c in SI if lap(c) == 0}
    forced = {}
    def inc(c):
        x, y = c
        return ((x-1, y), (x+1, y)) if ev(c) else ((x, y-1), (x, y+1))
    changed = True; rounds = 0
    while changed:
        changed = False; rounds += 1
        for (x, y) in SI:
            for a_, b_ in ((x, y), (x-1, y), (x, y-1), (x-1, y-1)):
                Q = [(a_, b_), (a_+1, b_), (a_, b_+1), (a_+1, b_+1)]
                if not all(q in SI for q in Q):
                    continue
                Qs = set(Q)
                for c in Q:
                    if c not in whites or c in forced:
                        continue
                    others = [q for q in Q if q != c]
                    if not all(lap(q) == -1 or (lap(q) == 0 and any(t in Qs for t in forced.get(q, ()))) for q in others):
                        continue
                    for o in inc(c):
                        if o not in Qs:
                            forced.setdefault(c, set()).add(o); changed = True; break
    return whites, forced, rounds


def classes(a, L):
    """Archive classes in LL coordinates (xL, yL); returns (class, direction) or None."""
    xL, yL = L
    h = yL - xL
    if h % 2 == 1 and -1 <= h <= a-3 and 1 <= xL <= a and yL != a-1 and (xL, h) != (1, -1):
        return ('L', 'S' if yL < a-1 else 'N')
    if h % 2 == 1 and a+1 <= h <= 2*a-1 and 0 <= xL <= a-1 and yL != 2*a-1 and (xL, h) != (a-1, 2*a-1):
        return ('U', 'S' if yL < 2*a-1 else 'N')
    if h == a-2 and 2 <= xL <= a:
        return ('E', 'E')
    if h == a and 0 <= xL <= a-2:
        return ('W', 'W')
    return None

def grade(a, c):
    x, y = c; h = y - x
    cl = classes(a, c)
    if cl is None: return None
    kind = cl[0]
    if kind == 'L': return abs(y - (a-1)) + (1 if (x == a and h == a-3) else 0)
    if kind == 'U': return abs(y - (2*a-1)) + (1 if (x == 0 and h == a+1) else 0)
    if kind == 'E': return x - 1 + (1 if x == a else 0)
    if kind == 'W': return a - 1 - x + (1 if x == 0 else 0)

for k in (1, 2, 3, 4):
    a = 2*k + 4; n = a - 1; d = a + 1
    SI, T = si_points(n, d)
    S = set(SI)
    assert all(NativeT(a, *c) for c in SI)
    lap = lambda c: lap_native(a, c)
    whites, forced, rounds = closure(S, lap)
    cl_ok = sum(1 for c in whites if classes(a, c) is not None)
    print("k=%d a=%d |SI|=%d whites=%d closure-forced=%d classified=%d" % (k, a, len(SI), len(whites), len(forced), cl_ok))
    bad = []
    for c in whites:
        cl = classes(a, c)
        if cl is None:
            bad.append(("noclass", c)); continue
        g = grade(a, c); t = list(forced[c])[0]; ok = False
        for a_, b_ in ((c[0], c[1]), (c[0]-1, c[1]), (c[0], c[1]-1), (c[0]-1, c[1]-1)):
            Q = [(a_, b_), (a_+1, b_), (a_, b_+1), (a_+1, b_+1)]
            if c not in Q or not all(q in S for q in Q) or t in Q: continue
            good = True
            for w in Q:
                if w == c or lap(w) == -1: continue
                cw = classes(a, w)
                if lap(w) == 0 and cw is not None and grade(a, w) < g and any(z in Q for z in forced.get(w, ())):
                    continue
                good = False; break
            if good: ok = True; break
        if not ok: bad.append((cl[0], c, g))
    print("   witness failures:", len(bad), bad[:5])
