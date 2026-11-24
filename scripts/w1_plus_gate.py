"""Q_plus gate (task 118, W1 base): exact-rank check of the edge predicate of prove_rank_plus.py, for odd d = 3..15.
rank = last alias offer (i-major), offers valPlus(shift) - i*2d - j*2(d+1); edge retained per the python `edge`."""
import sys
from collections import Counter
ALIASES = [(i, j) for i in range(-2, 3) for j in (-1, 0, 1)]

def shift(d, X, Y, i, j): return (X + i * d + j * (1 - d), Y + i + j * (d + 1))
def native(d, X, Y):
    return (2 - d <= X <= d and 0 <= Y <= d + 1 and 1 <= X + Y <= d + 2) or (X, Y) in [(0, 0), (2, d + 1)]
def H(d, X, Y): return Y == 0 and 1 <= X <= d
def V(d, X, Y): return (X, Y) == (0, 0) or (X + Y == 1 and 1 <= Y < d) or (X, Y) == (2 - d, d)
def free(d, X, Y): return H(d, X, Y) or V(d, X, Y)

def valPlus(d, X, Y):
    p = (X + Y) % 2
    if H(d, X, Y): return 2 * X + p - 4
    if V(d, X, Y): return 2 * Y - p
    if X <= 0 and X + Y == 2: return 2 * Y
    if X <= 0: return 2 * X + 4 * d - 4 + p
    return 4 * d - 2 * X + p

def isrep(d, X, Y):
    if free(d, X, Y): return True
    if not native(d, X, Y): return False
    for i, j in ALIASES:
        a, b = shift(d, X, Y, i, j)
        if free(d, a, b): return False
        if native(d, a, b) and (a > X or (a == X and b > Y)): return False
    return True

def ranksPlus(d, X, Y):
    out = []
    for i, j in ALIASES:
        a, b = shift(d, X, Y, i, j)
        if isrep(d, a, b):
            out.append(valPlus(d, a, b) - i * 2 * d - j * 2 * (d + 1))
    return out

def mn(a): return min(a, 0)
def corr(d, X, Y): return mn(X - 1) + (1 if (X, Y) in [(0, 0), (2, d + 1)] else 0)
def star(d, X, Y):
    if not native(d, X, Y): return False
    if (X + Y) % 2 == 0: return native(d, X - 1, Y) and native(d, X + 1, Y)
    return native(d, X, Y - 1) and native(d, X, Y + 1)
def lap(d, X, Y):
    if (X + Y) % 2 == 0: return corr(d, X - 1, Y) + corr(d, X + 1, Y) - 2 * corr(d, X, Y)
    return -1 + corr(d, X, Y - 1) + corr(d, X, Y + 1) - 2 * corr(d, X, Y)

def edgePlus(d, X, Y, dx, dy):
    """retained (dx,dy) from (X,Y), per prove_rank_plus.py edge"""
    par0 = (X + Y) % 2 == 0
    if (par0 and dy != 0) or ((not par0) and dx != 0): return False
    whites = []; hits = set()
    has_free = any(free(d, *shift(d, X, Y, i, j)) for i, j in ALIASES)
    for i, j in ALIASES:
        a, b = shift(d, X, Y, i, j)
        even = (a + b) % 2 == 0
        if H(d, a, b):
            whites.append('h'); hits.add((-1, 0) if even else (0, -1))
        if V(d, a, b):
            whites.append('v')
            if even: hits.add((-1, 0) if (a, b) == (2 - d, d) else (1, 0))
            else: hits.add((0, -1))
        cg = star(d, a, b) and lap(d, a, b) == 0 and even and (a <= 0 or a >= 2) and not has_free
        if cg:
            whites.append('c'); hits.add((-1, 0) if a <= 0 else (1, 0))
    if not whites: return True
    return (dx, dy) in hits

def family(d, X, Y):
    if free(d, X, Y): return 'F0 free'
    if (X, Y) == (2, d + 1): return 'F3 corner'
    if Y == d + 1: return 'F2 top'
    if (X, Y) == (d, 1): return 'F5 (d,1)'
    if X + Y == d + 2: return 'F4 anti'
    return 'F1 interior'

if __name__ == '__main__':
    for d in range(3, 16, 2):
        bad = []; n = 0; multi = 0; stat = Counter()
        for X in range(2 - d, d + 1):
            for Y in range(0, d + 2):
                if not native(d, X, Y) or free(d, X, Y) and False: continue
                if not native(d, X, Y): continue
                rp = ranksPlus(d, X, Y)
                if len(set(rp)) != 1: multi += 1; continue
                rv = rp[0]
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    if not edgePlus(d, X, Y, dx, dy): continue
                    n += 1
                    stat[(family(d, X, Y), (dx, dy))] += 1
                    rt = ranksPlus(d, X + dx, Y + dy)
                    if any(r >= rv for r in rt): bad.append(((X, Y), (dx, dy), rv, rt))
        print('d=%d retained %d multi %d violations %d' % (d, n, multi, len(bad)), bad[:3])
        if d == 9:
            for k in sorted(stat): print('   ', k, stat[k])
