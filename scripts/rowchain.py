"""Row-chain test: rows of a cell set are intervals, the nonempty rows are contiguous, and consecutive rows overlap.
Such a set is edge-connected and has no checkerboard vertex (see FLatticePaper/Tiles/RowChain.lean)."""
import sys
import standard_tiles as s

def rows(T):
    R = {}
    for (x, y) in T:
        R.setdefault(y, []).append(x)
    return {y: sorted(xs) for y, xs in R.items()}

def rowchain(T):
    R = rows(T)
    if not R: return True, "empty"
    ys = sorted(R)
    for y in ys:
        xs = R[y]
        if xs != list(range(xs[0], xs[-1] + 1)):
            return False, ("nonconvex row", y)
    if ys != list(range(ys[0], ys[-1] + 1)):
        return False, ("gap in rows", ys)
    for y in ys:
        if y + 1 in R:
            if not (set(R[y]) & set(R[y + 1])):
                return False, ("no overlap", y)
    return True, "ok"

if __name__ == "__main__":
    bad = []
    for d in range(2, 13):
        for name, T in (("stairF", s.stairF(d)), ("nstairN", s.nstairN(d)), ("ladderF", s.ladderF(d)),
                        ("nladderN", s.nladderN(d))):
            C = s.cellTile(T)
            ok, why = rowchain(C)
            if not ok: bad.append((name, d, why))
    print("base families d=2..12 failing:", bad[:10], len(bad))
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    nb = 0; tot = 0; ex = []
    for w in s.words(L):
        for T in (s.oddTile(w), s.evenTile(w)):
            tot += 1
            ok, why = rowchain(s.cellTile(T))
            if not ok:
                nb += 1
                if len(ex) < 5: ex.append((w, why))
    print("standard tiles words<=%d: rowchain fails %d of %d" % (L, nb, tot), ex)
