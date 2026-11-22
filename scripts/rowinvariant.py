"""Task 53 row invariant, numerics (step 1 of the row-chain route).
For each non-base word w up to length L, child kind (odd/even) and phase:
 - the bottom-to-top order of the copies attaining the minimum left end (lmin) and the maximum right end (rmax),
   with the number of runs (blocks) and the set of distinct orders;
 - whether every row of the child is an interval-union with no gap (abut);
 - for every switch between consecutive child rows: whether it is at the top row of the outgoing copy, the bottom row of
   the incoming copy, or neither (and whether both hold).
Usage: python3 rowinvariant.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words
from rowcopies import analyse
from siterows import row_intervals

if __name__ == "__main__":
    L = int(sys.argv[1])
    orders = {}
    gaps = Counter()
    sw = {}
    nwords = Counter()
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            pieces = cs[kind]
            rows = analyse(pieces)
            ys = sorted(rows)
            nwords[(kind, ph)] += 1
            if any(not rows[y][3] for y in ys): gaps[(kind, ph)] += 1
            rng = [(min(row_intervals(P)), max(row_intervals(P))) if row_intervals(P) else None for P in pieces]
            for role, idx in (("lmin", 1), ("rmax", 2)):
                runs = [rows[ys[0]][idx]] + [rows[ys[i + 1]][idx] for i in range(len(ys) - 1)
                                             if rows[ys[i]][idx] != rows[ys[i + 1]][idx]]
                orders.setdefault((kind, ph, role), Counter())[tuple(runs)] += 1
                c = sw.setdefault((kind, ph, role), Counter())
                for i in range(len(ys) - 1):
                    a, b = ys[i], ys[i + 1]
                    X, Y = rows[a][idx], rows[b][idx]
                    if X == Y: continue
                    topX, botY = rng[X][1], rng[Y][0]
                    key = ("top(out)" if a == topX else "") + (" bot(in)" if b == botY else "")
                    c[key.strip() or "NEITHER"] += 1
    print("words:", dict(nwords))
    print("rows with a gap (should be empty):", dict(gaps))
    for k in sorted(orders):
        print("order", k, sorted(orders[k].items(), key=lambda t: -t[1]))
    for k in sorted(sw):
        print("switch", k, dict(sw[k]))
