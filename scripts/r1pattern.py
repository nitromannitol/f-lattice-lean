"""Task 55 (R1, cell rows): the odd child, phase 0 (oddChildB false), end pattern 'pieces 5 and 4 only'.
Row y of the child is [A5, B4) where A5 = left end of piece 5, B4 = right end of piece 4, under the inequalities
  A5 < B5, A4 < B4, A5 <= A4 <= B5 <= B4, and pieces 0..3 empty on row y.
Checks these on all rows of this pattern for non-base words up to length L, and counts the rows that match the pattern.
Usage: python3 r1pattern.py L"""
import sys
from collections import Counter
from standard_tiles import words, state, childTiles
from r1cover import pieces_odd, cells, row_intervals

def main(L):
    tally = Counter()
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w):
            continue
        par, tO, tE = state(w)
        p, q = par
        b = sum(1 for x in w if x == 1) % 2 == 1
        if b:
            continue
        pcs = pieces_odd(False, tO, tE, p, q)
        sets = [cells(t, o) for (t, o) in pcs]
        child = childTiles(w, par, tO, tE)[0]
        for y in sorted({yy for (_, yy) in child}):
            iv = {}
            for i, s in enumerate(sets):
                xs = row_intervals(s, y)
                if xs:
                    iv[i] = (xs[0], xs[-1] + 1)
            if set(iv) != {4, 5}:
                continue
            A5, B5 = iv[5]; A4, B4 = iv[4]
            ok = (A5 < B5) and (A4 < B4) and (A5 <= A4 <= B5 <= B4)
            tally["rows"] += 1
            tally["ok" if ok else "fail"] += 1
            # the union is exactly [A5, B4)
            union = set(x for (x, yy) in child if yy == y)
            tally["union_is_interval" if union == set(range(A5, B4)) else "union_not_interval"] += 1
    print(dict(tally))

if __name__ == "__main__":
    main(int(sys.argv[1]))
