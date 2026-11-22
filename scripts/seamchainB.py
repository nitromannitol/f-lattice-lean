"""Task 54 numerics (B): the bottom chain of a non-base child. The bottom arc of the child (its forward arc w1 from (0,0))
is the concatenation of the bottom arcs of copies of the register tiles, joined by single i (north) steps.
For every copy k (its tile shifted by its offset), its own bottom arc (from its offset) must appear at a vertex of the
child's bottom arc. The chain: the copies whose arcs appear, in order, are consecutive with one N step between them, and
they cover the child's bottom arc. Counts: odd children (3 copies in the chain), even children (2 copies).
Usage: python3 seamchainB.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words, cellTile
from seamchain import walk_from, split_forward
N = (0, 1)


def bottom_arc(T, origin):
    loop = walk_from(T, origin)
    if loop is None: return None
    sp = split_forward(loop)
    if sp is None: return None
    w1 = sp[0]
    verts = [loop[k][0] for k in range(len(w1) + 1)]
    return verts, w1


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter(); bad = []
    for w in words(L):
        cs = copies(w)
        if cs is None: continue   # base words: separate lemma
        for kind in ("odd", "even"):
            pieces = cs[kind]
            child = cellTile(frozenset().union(*pieces))
            ch = bottom_arc(child, (0, 0))
            cnt[(kind, "child")] += 1
            if ch is None:
                cnt[(kind, "no_child_arc")] += 1; continue
            cverts, cw1 = ch
            index = {v: k for k, v in enumerate(cverts)}
            hits = []
            for k, P in enumerate(pieces):
                T = cellTile(P)
                if not T: continue
                # lower-left cell of the copy (minimal (y, x)); its corner is the origin of the copy's walk
                c0 = min(T, key=lambda c: (c[1], c[0]))
                arc = bottom_arc(T, c0)
                if arc is None: continue
                av, aw1 = arc
                # position in the child's bottom arc
                if c0 in index:
                    j = index[c0]
                    if cw1[j:j + len(aw1)] == aw1:
                        hits.append((j, k, len(aw1)))
            hits.sort()
            # chain: consecutive hits with one N step between, covering the child's arc
            ok = False
            if hits and hits[0][0] == 0:
                pos = 0; cur = None; good = True; used = []
                for j, k, ln in hits:
                    if j == pos and cur is None:
                        cur = (j, k, ln); pos = j + ln
                        used.append(k)
                    elif j == pos + 1 and cw1[pos] == N:
                        pos = j + ln; used.append(k)
                    else:
                        pass
                ok = (pos == len(cw1))
            cnt[(kind, "chain_covers_child_arc" if ok else "NO_chain")] += 1
            if not ok and len(bad) < 5: bad.append((w, kind, hits, cw1))
            if ok: cnt[(kind, "copies_in_chain", len(used))] += 1
    for k in sorted(cnt, key=str): print(k, cnt[k])
    print("bad (first):", bad[:3])
