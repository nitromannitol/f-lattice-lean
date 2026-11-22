"""Python port of the standard tiles (StandardTiles.lean) for numerical checks of task 53.

Sites are integer pairs. Fractions are pairs (num, den). A word is a tuple of digits 1, 2, 3.
Usage:  python3 standard_tiles.py MAXLEN     # checkerboard and connectivity tests of the cell tiles
"""
import sys
from functools import lru_cache
from collections import deque

Frac = tuple  # (num, den)

def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def shift(T, v): return frozenset((x + v[0], y + v[1]) for (x, y) in T)
def U(*Ts):
    out = set()
    for T in Ts: out |= set(T)
    return frozenset(out)

def texV1Odd(p): return (2 * p[1], 2 * p[0])
def texV1Even(q): return (q[1], q[0])
def texV2(f): return (f[0] - f[1], f[0] + f[1])

def rng(a, b): return range(a, b + 1)

def stairF(d):
    return frozenset((x, y) for x in rng(2 - d, d) for y in rng(0, d + 1) if (
        (2 - d <= x <= d and 0 <= y <= d + 1 and 1 <= x + y <= d + 2) or (x == 0 and y == 0) or (x == 2 and y == d + 1)))

def nstairF(d):
    return frozenset((x, y) for x in rng(0, d + 1) for y in rng(1, 2 * d - 1) if (
        (0 <= x <= d + 1 and 1 <= y <= 2 * d - 1 and -1 <= y - x <= d) or (x == 0 and y == d + 1) or (x == d + 1 and y == d - 1)))

def ladderF(d):
    out = set()
    for x in rng(2 - d, 2 * d):
        for y in rng(0, d + 2):
            a = ((x == 0 and y == 0) or (x == d + 2 and y == d + 2) or (x + y == d + 2 and 1 < y < d + 1) or
                 (2 - d <= x <= 2 * d and 0 <= y <= d + 2 and 1 <= x + y <= 2 * d + 3))
            b = (d <= x and y == 0) or (x <= 2 and y == d + 2)
            if a and not b: out.add((x, y))
    return frozenset(out)

def nladderF(d):
    out = set()
    for x in rng(-1, d + 1):
        for y in rng(1, 3 * d - 1):
            a = ((x == -1 and y == 2 * d + 1) or (x == d + 1 and y == d - 1) or (y - x == d and 0 < x < d) or
                 (-1 <= x <= d + 1 and 1 <= y <= 3 * d - 1 and -1 <= y - x <= 2 * d + 1))
            b = (x == -1 and y <= d + 1) or (x == d + 1 and 2 * d - 1 <= y)
            if a and not b: out.add((x, y))
    return frozenset(out)

def nstairN(d): return shift(nstairF(d), (0, -1))
def nladderN(d): return shift(nladderF(d), (0, -1))

zeroTile = frozenset({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)})
oneTile = frozenset({(0, 0), (0, 1), (1, 0), (1, 1)})

def oddChildB(b, T1, T2, p, q):
    if b:
        return U(shift(T2, texV1Odd(p)), shift(T2, add(texV1Odd(p), texV1Even(q))), shift(T2, texV2(p)),
                 shift(T2, add(texV2(p), texV1Even(q))), T1,
                 shift(T1, add(add(texV1Even(q), texV1Even(q)), texV2(q))))
    return U(T2, shift(T2, texV1Even(q)), shift(T2, add(texV1Odd(p), texV2(p))),
             shift(T2, add(add(texV1Odd(p), texV2(p)), texV1Even(q))),
             shift(T1, add(texV1Even(q), texV1Even(q))), shift(T1, texV2(q)))

def evenChildB(b, T1, T2, p, q):
    if b:
        return U(shift(T2, texV1Odd(p)), shift(T2, add(texV2(p), texV2(p))), T1, shift(T1, texV2(p)),
                 shift(T1, add(texV1Even(q), texV2(q))),
                 shift(T1, add(add(texV1Even(q), texV2(q)), texV2(p))))
    return U(T2, shift(T2, add(texV1Odd(p), add(texV2(p), texV2(p)))), shift(T1, texV1Even(q)),
             shift(T1, add(texV1Even(q), texV2(p))), shift(T1, texV2(q)),
             shift(T1, add(texV2(q), texV2(p))))

def parents_step(par, d):
    odd, even = par
    cur_odd = (odd[0] + even[0], odd[1] + even[1])
    cur_even = (2 * odd[0] + even[0], 2 * odd[1] + even[1])
    if d == 1: return (cur_odd, cur_even)
    if d == 2: return (cur_odd, even)
    return (odd, cur_even)

ROOT = ((0, 1), (1, 1))

def childTiles(w, par, tO, tE):
    n = len(w)
    if n == 0:
        return nstairN(3), stairF(3)
    if all(x == 3 for x in w):
        return ladderF(2 * n + 2), stairF(2 * n + 3)
    if all(x == 2 for x in w):
        return nstairN(2 * n + 3), nladderN(2 * n + 2)
    phase = sum(1 for x in w if x == 1) % 2
    b = phase == 1
    return oddChildB(b, tO, tE, par[0], par[1]), evenChildB(b, tO, tE, par[0], par[1])

@lru_cache(maxsize=None)
def state(w):
    if not w:
        return ROOT, zeroTile, oneTile
    pre = w[:-1]
    par, tO, tE = state(pre)
    d = w[-1]
    c1, c2 = childTiles(pre, par, tO, tE)
    newpar = parents_step(par, d)
    if d == 1: return newpar, c1, c2
    if d == 2: return newpar, c1, tE
    return newpar, tO, c2

def oddTile(w):
    par, tO, tE = state(w)
    return childTiles(w, par, tO, tE)[0]

def evenTile(w):
    par, tO, tE = state(w)
    return childTiles(w, par, tO, tE)[1]

def cellTile(P):
    """cells (lower-left corners a in P) whose four corners lie in P"""
    return frozenset(a for a in P if all(c in P for c in [a, (a[0] + 1, a[1]), (a[0], a[1] + 1), (a[0] + 1, a[1] + 1)]))

def checker_at(T, v):
    x, y = v
    a = (x, y) in T; b = (x - 1, y) in T; c = (x - 1, y - 1) in T; d = (x, y - 1) in T
    return (a and c and not b and not d) or (b and d and not a and not c)

def has_checker(T):
    verts = set()
    for (x, y) in T:
        verts |= {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
    return any(checker_at(T, v) for v in verts)

def connected(T):
    if not T: return True
    start = min(T)
    seen = {start}; dq = deque([start])
    while dq:
        x, y = dq.popleft()
        for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if n in T and n not in seen:
                seen.add(n); dq.append(n)
    return len(seen) == len(T)

def words(L):
    cur = [()]
    for n in range(L + 1):
        for w in cur: yield w
        cur = [w + (d,) for w in cur for d in (1, 2, 3)] if n < L else []

if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = nchk = nconn = 0
    bad_chk = []; bad_conn = []
    for w in words(L):
        for name, f in (("odd", oddTile), ("even", evenTile)):
            T = cellTile(f(w))
            cnt += 1
            if has_checker(T): nchk += 1; bad_chk.append((name, w))
            if not connected(T): nconn += 1; bad_conn.append((name, w))
    print("tiles", cnt, "with checkerboard", nchk, "disconnected cell tiles", nconn)
    print("first checkerboard:", bad_chk[:5])
    print("first disconnected:", bad_conn[:5])
