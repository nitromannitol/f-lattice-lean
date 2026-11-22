"""Task 53 row invariant, numerics (walk form): the boundary loop of a standard tile as four monotone arcs.
The boundary of a cell tile is traced counterclockwise (cell on the left). The tile is a rectilinear loop; we test
whether some start vertex splits it into four consecutive arcs of the shape
   arc1 in {E,N}*, arc2 in {N,W}*, arc3 in {W,S}*, arc4 in {S,E}*
(the shape of w1 * w2 * hat(rev w1) * hat(rev w2) with w1 in {1,i}, w2 in {i,-1}). For such a start, every height b has
exactly one north step (in arc1 or arc2, at x = xN(b)) and one south step (in arc3 or arc4, at x = xS(b)), and the cell
row b is [xS(b), xN(b)). We check this against the tile and the row-chain overlap of consecutive rows.
Usage: python3 arcs.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words, oddTile, evenTile, state
E, N, W, S = (1, 0), (0, 1), (-1, 0), (0, -1)
NAME = {E: 'E', N: 'N', W: 'W', S: 'S'}


def boundary_edges(T):
    out = {}
    for (x, y) in T:
        if (x, y - 1) not in T: out.setdefault((x, y), []).append(((x + 1, y), E))
        if (x + 1, y) not in T: out.setdefault((x + 1, y), []).append(((x + 1, y + 1), N))
        if (x, y + 1) not in T: out.setdefault((x + 1, y + 1), []).append(((x, y + 1), W))
        if (x - 1, y) not in T: out.setdefault((x, y + 1), []).append(((x, y), S))
    return out


def trace(T):
    """the single boundary loop as (start vertex, list of (vertex, direction)); None if not a single simple loop"""
    out = boundary_edges(T)
    if not out: return None
    if any(len(v) != 1 for v in out.values()): return None
    start = min(out)
    loop = []; v = start
    while True:
        (nv, d), = out[v]
        loop.append((v, d))
        v = nv
        if v == start: break
        if len(loop) > len(out) + 1: return None
    if len(loop) != sum(len(v) for v in out.values()): return None
    return loop


def arc_split(dirs):
    """positions i1<=i2<=i3 with dirs[:i1] in {E,N}*, dirs[i1:i2] in {N,W}*, dirs[i2:i3] in {W,S}*, dirs[i3:] in {S,E}*"""
    n = len(dirs)
    A = {E, N}; B = {N, W}; C = {W, S}; D = {S, E}
    def ok(lo, hi, cls): return all(dirs[k] in cls for k in range(lo, hi))
    for i1 in range(n + 1):
        if not ok(0, i1, A): break
        for i2 in range(i1, n + 1):
            if not ok(i1, i2, B): break
            for i3 in range(i2, n + 1):
                if not ok(i2, i3, C): break
                if ok(i3, n, D): return (i1, i2, i3)
    return None


def find_start(loop):
    """a rotation of the loop with the four-arc shape; returns (rotation index, split) or None"""
    dirs = [d for _, d in loop]
    n = len(dirs)
    for r in range(n):
        rot = dirs[r:] + dirs[:r]
        sp = arc_split(rot)
        if sp is not None:
            return r, sp
    return None


def row_columns(loop, r, sp):
    """xN(b) and xS(b) for a rotation r and split sp"""
    n = len(loop)
    verts = [loop[(r + k) % n][0] for k in range(n)]
    dirs = [loop[(r + k) % n][1] for k in range(n)]
    xN, xS = {}, {}
    i1, i2, i3 = sp
    for k in range(n):
        x, y = verts[k]
        if dirs[k] == N:
            # north steps are in arc1 or arc2 (indices < i2)
            assert k < i2
            xN[y] = x
        if dirs[k] == S:
            assert k >= i2
            xS[y - 1] = x
    return xN, xS


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    bad = []
    for w in words(L):
        par, tO, tE = state(w)
        for name, T in (("odd", oddTile(w)), ("even", evenTile(w))):
            cnt[(name, "tiles")] += 1
            loop = trace(T)
            if loop is None:
                cnt[(name, "not_simple_loop")] += 1; bad.append((w, name, "loop")); continue
            fs = find_start(loop)
            if fs is None:
                cnt[(name, "no_four_arc_start")] += 1; bad.append((w, name, "arcs")); continue
            r, sp = fs
            xN, xS = row_columns(loop, r, sp)
            rows = sorted(set(y for _, y in T))
            ok_rows = all(set(range(xS[b], xN[b])) == {x for x, y in T if y == b} for b in rows)
            cnt[(name, "rows_match_interval")] += ok_rows
            cnt[(name, "heights_match")] += (set(xN) == set(rows) and set(xS) == set(rows))
            overlap = all(max(xS[b], xS[b + 1]) < min(xN[b], xN[b + 1]) for b in rows[:-1]) and all(xS[b] < xN[b] for b in rows)
            cnt[(name, "row_chain_overlap")] += overlap
    for k in sorted(cnt): print(k, cnt[k])
    print("failures (first 5):", bad[:5])
