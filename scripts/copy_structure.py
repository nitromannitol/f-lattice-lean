"""Task 53 numerics: the six copies of the register tiles in the odd and even children of a recursion word.

For a non-base word w, each child is the union of translated copies of its two register tiles (oddChildB/evenChildB).
This script checks, for words up to a given length: (a) each copy's cell tile is edge-connected, (b) the copies' cell
tiles are connected through shared cells, (c) every cell of the cell tile of the union that lies in no copy's cell
tile is edge-adjacent to a cell of some copy, (d) the union's cell tile has no checkerboard vertex.
Usage: python3 copy_structure.py MAXLEN
"""
import sys
from standard_tiles import (state, childTiles, cellTile, connected, has_checker, shift, texV1Odd, texV1Even, texV2,
                            words, stairF, nstairN, ladderF, nladderN)


def copies_odd(w):
    par, tO, tE = state(w)
    p, q = par[0], par[1]
    if len(w) == 0 or all(x == 3 for x in w) or all(x == 2 for x in w):
        return None
    phase = sum(1 for x in w if x == 1) % 2
    if phase == 1:
        return [shift(tE, texV1Odd(p)), shift(tE, (texV1Odd(p)[0] + texV1Even(q)[0], texV1Odd(p)[1] + texV1Even(q)[1])),
                shift(tE, texV2(p)), shift(tE, (texV2(p)[0] + texV1Even(q)[0], texV2(p)[1] + texV1Even(q)[1])),
                tO, shift(tO, (2 * texV1Even(q)[0] + texV2(q)[0], 2 * texV1Even(q)[1] + texV2(q)[1]))]
    return [tE, shift(tE, texV1Even(q)), shift(tE, (texV1Odd(p)[0] + texV2(p)[0], texV1Odd(p)[1] + texV2(p)[1])),
            shift(tE, (texV1Odd(p)[0] + texV2(p)[0] + texV1Even(q)[0], texV1Odd(p)[1] + texV2(p)[1] + texV1Even(q)[1])),
            shift(tO, (2 * texV1Even(q)[0], 2 * texV1Even(q)[1])), shift(tO, texV2(q))]


def adjacent_to(x, S):
    return any(n in S for n in ((x[0] + 1, x[1]), (x[0] - 1, x[1]), (x[0], x[1] + 1), (x[0], x[1] - 1)))


def pieces_connected(pieces):
    """the pieces (sets of cells) are connected through shared cells"""
    if not pieces: return True
    seen = {0}; frontier = [0]
    while frontier:
        i = frontier.pop()
        for j in range(len(pieces)):
            if j not in seen and pieces[i] & pieces[j]:
                seen.add(j); frontier.append(j)
    return len(seen) == len(pieces)


def check(w):
    res = {"copy_disconnected": 0, "pieces_disconnected": 0, "extra_nonadjacent": 0, "checker": 0}
    cs = copies_odd(w)
    if cs is None: return res
    pieces = [cellTile(c) for c in cs]
    for c in pieces:
        if c and not connected(c): res["copy_disconnected"] += 1
    if not pieces_connected([p for p in pieces if p]): res["pieces_disconnected"] += 1
    union_cells = cellTile(frozenset().union(*cs))
    covered = frozenset().union(*pieces)
    for x in union_cells:
        if x not in covered and not adjacent_to(x, covered): res["extra_nonadjacent"] += 1
    if has_checker(union_cells): res["checker"] += 1
    return res


if __name__ == "__main__":
    L = int(sys.argv[1])
    tot = {}
    n = 0
    for w in words(L):
        r = check(w)
        if r is None: continue
        n += 1
        for k, v in r.items(): tot[k] = tot.get(k, 0) + v
    print("non-base odd children", n, tot)
