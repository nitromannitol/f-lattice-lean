"""Task 54 numerics: the seam facts of StandardBoundaryWord on the tiles of words of length 1..L (odd and even children,
2184 tiles at L = 6).
(A) forward four-arc shape: the boundary loop from the lower-left vertex (0,0) is w1 w2 (-w1) (-w2) with w1 in {E,N}*,
    w2 in {N,W}* (the Lean boundaryWordOf convention), and the walk is the boundary of the cell tile.
(B) bottom chain: for a non-base word, the bottom arc of the child (w1, from (0,0)) is the concatenation of the bottom arcs
    of some copies of the register tiles (each copy's arc, shifted to its offset), joined by single i steps.
Usage: python3 seamchain.py L"""
import sys
from collections import Counter
from standard_tiles import words, oddTile, evenTile, cellTile, shift
from arcs import boundary_edges
from junctions import copies
E, N, W, S = (1, 0), (0, 1), (-1, 0), (0, -1)


def walk_from(T, start):
    out = boundary_edges(T)
    if start not in out or any(len(v) != 1 for v in out.values()):
        return None
    loop = []; v = start
    while True:
        (nv, d), = out[v]
        loop.append((v, d)); v = nv
        if v == start: break
        if len(loop) > len(out) + 1: return None
    if len(loop) != sum(len(x) for x in out.values()): return None
    return loop


def split_forward(loop):
    """split the loop from its start into (w1, w2, w3, w4) with the forward shape, or None"""
    dirs = [d for _, d in loop]
    n = len(dirs)
    A = {E, N}; B = {N, W}; C = {W, S}; D = {S, E}
    for i1 in range(n + 1):
        if not all(d in A for d in dirs[:i1]): break
        for i2 in range(i1, n + 1):
            if not all(d in B for d in dirs[i1:i2]): break
            for i3 in range(i2, n + 1):
                if not all(d in C for d in dirs[i2:i3]): break
                if all(d in D for d in dirs[i3:]):
                    return dirs[:i1], dirs[i1:i2], dirs[i2:i3], dirs[i3:]
    return None


def arc1_vertices(loop, w1len):
    return [loop[k][0] for k in range(w1len + 1)] if w1len > 0 else [loop[0][0]]


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    bad = []
    for w in words(L):
        for kind in ("odd", "even"):
            tile = oddTile(w) if kind == "odd" else evenTile(w)
            T = cellTile(tile)
            cnt[(kind, "tiles")] += 1
            loop = walk_from(T, (0, 0))
            if loop is None:
                cnt[(kind, "no_loop_from_origin")] += 1; bad.append((w, kind, "loop")); continue
            sp = split_forward(loop)
            if sp is None:
                cnt[(kind, "not_forward_shape")] += 1; bad.append((w, kind, "shape")); continue
            w1, w2, w3, w4 = sp
            neg = lambda L_: [(-x, -y) for x, y in L_]
            cnt[(kind, "forward_shape")] += 1
            cnt[(kind, "arc3_is_neg_arc1")] += (w3 == neg(w1))
            cnt[(kind, "arc4_is_neg_arc2")] += (w4 == neg(w2))
            if not (w3 == neg(w1) and w4 == neg(w2)):
                bad.append((w, kind, "neg"))
    print("(A) per tile:", dict(cnt))
    print("bad examples:", bad[:5])
