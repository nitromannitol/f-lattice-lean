"""Task 53 step 2 numerics: the piece pairs of a child that are joined (by a bridging cell or by adjacency) for every
non-base word. Such pairs give a uniform junction structure for the induction.
Usage: python3 junction_core.py L"""
import sys
from junctions import copies, adj
from standard_tiles import cellTile, words
from functools import reduce


def joined_pairs(pieces):
    U = cellTile(frozenset().union(*pieces))
    P = [cellTile(c) for c in pieces]
    covered = frozenset().union(*P)
    n = len(pieces)
    pairs = set()
    for i in range(n):
        for j in range(i + 1, n):
            if any(adj(a, b) for a in P[i] for b in P[j]):
                pairs.add((i, j))
    for x in U:
        if x in covered: continue
        touched = [i for i in range(n) if any(adj(x, c) for c in P[i])]
        for i in touched:
            for j in touched:
                if i < j: pairs.add((i, j))
    return pairs


def connected_graph(n, pairs):
    seen = {0}; st = [0]
    while st:
        i = st.pop()
        for a, b in pairs:
            for u, v in ((a, b), (b, a)):
                if u == i and v not in seen: seen.add(v); st.append(v)
    return len(seen) == n


if __name__ == "__main__":
    L = int(sys.argv[1])
    core = {"odd": None, "even": None}
    cnt = 0
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        cnt += 1
        for kind in ("odd", "even"):
            pr = joined_pairs(cs[kind])
            core[kind] = pr if core[kind] is None else core[kind] & pr
    print("words", cnt)
    for kind in ("odd", "even"):
        print(kind, "pairs joined for every word:", sorted(core[kind]), "connected:", connected_graph(6, core[kind]))
