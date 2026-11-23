"""Numerical replay of the Q_minus strict-rank gates of w3's pure3 note (prove_rank.py, symbolic UNSAT claims), for concrete odd d.
Translation of prove_rank.py: aliases (i,j), i in [-2,2], j in {-1,0,1}; shift(X,Y,i,j) = (X + i d + j(1-d), Y + i + j(d+1));
native, H, V, free, rep, val (Q_minus), rank (last alias with rep true wins, as z3's If-chain), corr, star, lap, edge.
Gate (per direction): for native root with rep(root) and edge(root,dir) and rep(target): rank(target) < rank(root)."""
import sys
from collections import Counter

ALIASES = [(i, j) for i in range(-2, 3) for j in (-1, 0, 1)]

def make(d):
    def shift(X, Y, i, j): return (X + i * d + j * (1 - d), Y + i + j * (d + 1))
    def native(X, Y):
        return ((2 - d <= X <= d and 0 <= Y <= d + 1 and 1 <= X + Y <= d + 2) or (X == 0 and Y == 0) or (X == 2 and Y == d + 1))
    def H(X, Y): return Y == 0 and 1 <= X <= d
    def V(X, Y): return (X == 0 and Y == 0) or (X + Y == 1 and 1 <= Y < d) or (X == 2 - d and Y == d)
    def free(X, Y): return H(X, Y) or V(X, Y)
    def rep(X, Y):
        if free(X, Y): return True
        if not native(X, Y): return False
        for i, j in ALIASES:
            a, b = shift(X, Y, i, j)
            if free(a, b): return False
            if native(a, b) and (a > X or (a == X and b > Y)): return False
        return True
    def val(X, Y):
        p = (X + Y) % 2
        if H(X, Y): return 2 * X + p
        if V(X, Y): return -2 * Y - p
        if X + Y == d + 1 and X >= 1: return 2 * X
        if X <= 0: return 2 * X - 4 + p
        return 4 * d - 4 - 2 * X + p
    def offer(X, Y):
        r = None
        for i, j in ALIASES:
            a, b = shift(X, Y, i, j)
            if rep(a, b):
                r = val(a, b) - i * 2 * d + j * 2 * (d + 1)
        return r
    def rank(X, Y):
        return offer(X, Y)
    def corr(X, Y):
        return min(X - 1, 0) + (1 if ((X == 0 and Y == 0) or (X == 2 and Y == d + 1)) else 0)
    def star(X, Y):
        if not native(X, Y): return False
        if (X + Y) % 2 == 0: return native(X - 1, Y) and native(X + 1, Y)
        return native(X, Y - 1) and native(X, Y + 1)
    def lap(X, Y):
        if (X + Y) % 2 == 0: return corr(X - 1, Y) + corr(X + 1, Y) - 2 * corr(X, Y)
        return -1 + corr(X, Y - 1) + corr(X, Y + 1) - 2 * corr(X, Y)
    def edge(X, Y, dx, dy):
        whites = []; hits = []
        for i, j in ALIASES:
            a, b = shift(X, Y, i, j)
            hg = H(a, b); vg = V(a, b)
            even = (a + b) % 2 == 0
            hx = -1 if even else 0
            hy = 0 if even else (1 if a == d else -1)
            vx = -1 if even else 0
            vy = 0 if even else 1
            cg = star(a, b) and lap(a, b) == 0 and even and (a <= 0 or a >= 2) and not any(free(*shift(X, Y, ii, jj)) for ii, jj in ALIASES)
            cx = -1 if a <= 0 else 1
            whites += [hg, vg, cg]
            hits += [hg and hx == dx and hy == dy, vg and vx == dx and vy == dy, cg and cx == dx and dy == 0]
        parity_ok = (dy == 0) if (X + Y) % 2 == 0 else (dx == 0)
        return parity_ok and ((not any(whites)) or any(hits))
    return dict(native=native, rep=rep, rank=rank, edge=edge, val=val)

def check(d):
    F = make(d)
    c = Counter(); bad = []
    pts = [(X, Y) for X in range(2 - d, d + 1) for Y in range(0, d + 2)] + [(0, 0), (2, d + 1)]
    pts = [p for p in set(pts) if F['native'](*p)]
    for (X, Y) in pts:
        r = F['rank'](X, Y)
        if r is None: c['root without offer'] += 1; continue
        c['roots with offer'] += 1
        for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            if not F['edge'](X, Y, dx, dy): continue
            tx, ty = X + dx, Y + dy
            ru = F['rank'](tx, ty)
            if ru is None: c['target without offer (skipped)'] += 1; continue
            c['retained edge, target has offer'] += 1
            if not ru < r:
                bad.append(((X, Y), (dx, dy), r, (tx, ty), ru))
            else:
                c['strict drop ok'] += 1
    return c, bad

if __name__ == '__main__':
    for d in range(3, 16, 2):
        c, bad = check(d)
        print('d=%d' % d, dict(c), 'violations:', len(bad), bad[:2])
