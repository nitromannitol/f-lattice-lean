"""Task 55 (R1, first pattern): the slack of the three comparisons on all rows of the pattern (odd child, phase 0, pieces 4
and 5 only, T2 pieces empty). Slacks: a = A4 - A5, b = B5 - A4, c = B4 - B5; each must be >= 0 for the child row to be
[A5, B4). Reports the minimum slack and the number of zero-slack rows. Usage: python3 r1slack.py"""
from standard_tiles import words, state, childTiles
from r1cover import pieces_odd, cells, row_intervals

def main(Ls=(3, 4, 5)):
    mins = {"a": None, "b": None, "c": None}; zero = {"a": 0, "b": 0, "c": 0}; n = 0
    for L in Ls:
        for w in words(L):
            if not w or all(x == 3 for x in w) or all(x == 2 for x in w): continue
            par, tO, tE = state(w); p, q = par
            if sum(1 for x in w if x == 1) % 2 == 1: continue
            sets = [cells(t, o) for (t, o) in pieces_odd(False, tO, tE, p, q)]
            child = childTiles(w, par, tO, tE)[0]
            for y in sorted({yy for (_, yy) in child}):
                iv = {}
                for i, s in enumerate(sets):
                    xs = row_intervals(s, y)
                    if xs: iv[i] = (xs[0], xs[-1] + 1)
                if set(iv) != {4, 5}: continue
                A5, B5 = iv[5]; A4, B4 = iv[4]
                n += 1
                for k, v in (("a", A4 - A5), ("b", B5 - A4), ("c", B4 - B5)):
                    if mins[k] is None or v < mins[k][0]:
                        mins[k] = (v, ''.join(map(str, w)), y, p, q)
                    if v == 0: zero[k] += 1
    print("rows", n)
    for k in ("a", "b", "c"): print(k, "min slack (value, word, row, p, q)", mins[k], "zero-slack rows", zero[k])

if __name__ == "__main__":
    main()
