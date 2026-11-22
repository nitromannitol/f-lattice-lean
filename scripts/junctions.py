"""Task 53 step 2 numerics: how the copies of the register tiles in the odd and even children are joined.

For each non-base word w (up to length L) and each child (odd/even), the child is the union of six translated
copies (pieces) of the registers tO / tE (as in oddChildB / evenChildB). Let U be the cell tile of the union,
P_i the cell tile of the i-th copy, C the cells of U lying in no piece (bridging cells).
Reported: edge-connectivity of U, whether the pieces are joined through shared cells and bridging cells
(piece graph), the number of bridging cells, and the piece pairs joined by a bridging cell.
Usage: python3 junctions.py L
"""
import sys
from collections import Counter
from standard_tiles import (state, cellTile, connected, has_checker, shift, texV1Odd, texV1Even, texV2, words)


def add(*vs):
    return (sum(v[0] for v in vs), sum(v[1] for v in vs))


def copies(w):
    """(kind, pieces) with kind 'odd' or 'even' for the non-base word w; None for base words"""
    if len(w) == 0 or all(x == 3 for x in w) or all(x == 2 for x in w):
        return None
    par, tO, tE = state(w)
    p, q = par[0], par[1]
    phase = sum(1 for x in w if x == 1) % 2
    O1p, O2p, E1q, E2p, E2q, O1q = texV1Odd(p), texV2(p), texV1Even(q), texV2(p), texV2(q), texV1Even(q)
    odd = {True: [shift(tE, O1p), shift(tE, add(O1p, E1q)), shift(tE, texV2(p)), shift(tE, add(texV2(p), E1q)),
                  tO, shift(tO, add(E1q, E1q, texV2(q)))],
           False: [tE, shift(tE, E1q), shift(tE, add(O1p, texV2(p))), shift(tE, add(O1p, texV2(p), E1q)),
                   shift(tO, add(E1q, E1q)), shift(tO, texV2(q))]}[phase == 1]
    even = {True: [shift(tE, O1p), shift(tE, add(texV2(p), texV2(p))), tO, shift(tO, texV2(p)),
                   shift(tO, add(E1q, texV2(q))), shift(tO, add(E1q, texV2(q), texV2(p)))],
            False: [tE, shift(tE, add(O1p, texV2(p), texV2(p))), shift(tO, E1q), shift(tO, add(E1q, texV2(p))),
                    shift(tO, texV2(q)), shift(tO, add(texV2(q), texV2(p)))]}[phase == 1]
    return {"odd": odd, "even": even}


def adj(a, b):
    return abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1


def analyse(pieces):
    U = cellTile(frozenset().union(*pieces))
    P = [cellTile(c) for c in pieces]
    covered = frozenset().union(*P)
    bridge = [x for x in U if x not in covered]
    n = len(pieces)
    edges = set()
    for i in range(n):
        for j in range(i + 1, n):
            if any(adj(a, b) for a in P[i] for b in P[j]):
                edges.add((i, j))
    pairs = Counter()
    for x in bridge:
        touched = tuple(i for i in range(n) if any(adj(x, c) for c in P[i]))
        for i in touched:
            for j in touched:
                if i < j:
                    edges.add((i, j))
        pairs[touched] += 1
    # graph connectivity of the pieces, with the bridging cells
    seen = {0}; stack = [0]
    while stack:
        i = stack.pop()
        for (a, b) in edges:
            for u, v in ((a, b), (b, a)):
                if u == i and v not in seen:
                    seen.add(v); stack.append(v)
    return {"U_connected": connected(U), "checker": has_checker(U), "pieces_connected": len(seen) == n,
            "bridge": len(bridge), "bridge_patterns": pairs, "pieces_with_empty": sum(1 for p in P if not p),
            "pieces_nonconnected": sum(1 for p in P if p and not connected(p))}


if __name__ == "__main__":
    L = int(sys.argv[1])
    tot = Counter()
    pat = {"odd": Counter(), "even": Counter()}
    nw = 0
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        nw += 1
        for kind in ("odd", "even"):
            r = analyse(cs[kind])
            tot[(kind, "U_connected", r["U_connected"])] += 1
            tot[(kind, "checker", r["checker"])] += 1
            tot[(kind, "pieces_connected", r["pieces_connected"])] += 1
            tot[(kind, "pieces_nonconnected")] += r["pieces_nonconnected"]
            tot[(kind, "empty_piece")] += r["pieces_with_empty"]
            for k, v in r["bridge_patterns"].items():
                pat[kind][k] += v
    print("words", nw)
    for k, v in sorted(tot.items(), key=str):
        print(k, v)
    for kind in ("odd", "even"):
        print(kind, "bridging patterns (pieces touched : count):", sorted(pat[kind].items(), key=lambda t: -t[1]))
