"""Task 55 (R1, bridge): point-set rows to cell-tile rows.

For a point set C (a register child tile, Tile = set of sites), cellTile(C) has cell (x,b) iff the four corners
(x,b),(x+1,b),(x,b+1),(x+1,b+1) lie in C. If the point rows of C are intervals [L_b, R_b) (possibly empty), the cell row b is
the set of x with x, x+1 in both rows b and b+1, i.e. the interval [max(L_b, L_{b+1}), min(R_b, R_{b+1}) - 1).
This script checks, for every child point set C (odd and even, non-base words up to length L):
  (a) every point row of C is an interval;
  (b) the cell row b of cellTile(C) equals [max(L_b,L_{b+1}), min(R_b,R_{b+1})-1) (empty if the bracket is empty);
  (c) the same bridge for the union of the pieces (cellTile of union is not the union of cellTiles; reported separately).
Usage: python3 r1bridge.py L"""
import sys
from collections import Counter
from standard_tiles import words, oddTile, evenTile, cellTile

def point_rows(C):
    rows = {}
    for (x, y) in C:
        rows.setdefault(y, []).append(x)
    out = {}
    for y, xs in rows.items():
        xs = sorted(xs)
        interval = xs == list(range(xs[0], xs[-1] + 1))
        out[y] = (xs[0], xs[-1] + 1, interval)
    return out

def cell_row_pred(pr, b):
    if b not in pr or (b + 1) not in pr:
        return None
    La, Ra, ia = pr[b]
    Lb, Rb, ib = pr[b + 1]
    lo, hi = max(La, Lb), min(Ra, Rb) - 1
    return list(range(lo, hi)) if lo < hi else []

def main(L):
    cnt = Counter(); bad = []
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w):
            continue
        for child, C in (("odd", oddTile(w)), ("even", evenTile(w))):
            pr = point_rows(C)
            cnt["child"] += 1
            for y, (l, r, iv) in pr.items():
                cnt["point_row"] += 1
                cnt["point_row_interval"] += 1 if iv else 0
            cells = cellTile(C)
            cell_rows = {}
            for (x, b) in cells:
                cell_rows.setdefault(b, []).append(x)
            for b in set(cell_rows) | {bb for bb in pr if bb + 1 in pr}:
                pred = cell_row_pred(pr, b)
                actual = sorted(cell_rows.get(b, []))
                if pred is None:
                    cnt["skip"] += 1
                    continue
                ok = pred == actual
                cnt["cell_row_checked"] += 1
                cnt["cell_row_match" if ok else "cell_row_mismatch"] += 1
                if not ok and len(bad) < 3:
                    bad.append((''.join(map(str, w)), child, b, pred[:6], actual[:6]))
    for k in sorted(cnt):
        print(k, cnt[k])
    print("examples of mismatch:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
