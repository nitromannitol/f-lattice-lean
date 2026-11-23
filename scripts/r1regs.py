"""Task 55 (R1 register comparisons): for the odd child, phase 0, end pattern with pieces 5 and 4 only, the register
data: the row range of the register tile T1 = tO, its row ends at the two offset heights, and the parent fraction q.
Prints one line per row of the pattern: word, child row y, q=(num,den), the row range [ymin,ymax] of tO, and the row
ends lo,hi of tO at heights y-(num+den) (piece 5) and y-2num (piece 4), together with the four interval ends A5,B5,A4,B4.
Usage: python3 r1regs.py L"""
import sys
from standard_tiles import words, state, childTiles
from r1cover import pieces_odd, cells, row_intervals

def row_ends(T, c):
    xs = [x for (x, y) in T if y == c]
    if not xs:
        return None
    return (min(xs), max(xs) + 1)

def main(L):
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w):
            continue
        par, tO, tE = state(w)
        p, q = par
        if sum(1 for x in w if x == 1) % 2 == 1:
            continue
        sets = [cells(t, o) for (t, o) in pieces_odd(False, tO, tE, p, q)]
        child = childTiles(w, par, tO, tE)[0]
        ysO = sorted({y for (_, y) in tO})
        ymin, ymax = ysO[0], ysO[-1]
        for y in sorted({yy for (_, yy) in child}):
            iv = {}
            for i, s in enumerate(sets):
                xs = row_intervals(s, y)
                if xs:
                    iv[i] = (xs[0], xs[-1] + 1)
            if set(iv) != {4, 5}:
                continue
            n, d = q
            r5 = row_ends(tO, y - (n + d))
            r4 = row_ends(tO, y - 2 * n)
            print(f"w={''.join(map(str,w))} y={y} q=({n},{d}) tO_rows=[{ymin},{ymax}] "
                  f"lo/hi@y-(n+d)={r5} lo/hi@y-2n={r4} A5,B5,A4,B4={iv[5]+iv[4]}")

if __name__ == "__main__":
    main(int(sys.argv[1]))
