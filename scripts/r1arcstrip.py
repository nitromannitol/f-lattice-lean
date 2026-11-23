"""Task 55 (R1 structure theorem, numerical form): the arcs of the register tiles lie in a strip around their chord.

For a word v (length 1..L, not all 2, not all 3) the register tiles oddTile v and evenTile v (point sets) are turned into cell
tiles; their first and second forward arcs (from (0,0)) are w1 and w2 (letters 1 and i). For an arc u with X ones and Y i's,
colN(s) is the x-coordinate of the (s+1)-st north step (s = 0..Y-1). The chord is the line from (0,0) to (X,Y): slope X/Y.
Measure D(u) = max over s of |colN(s) - s*X/Y|, and report its distribution by arc (w1 or w2) and child type.
Usage: python3 r1arcstrip.py L"""
import sys
from collections import Counter
from fractions import Fraction
from standard_tiles import words, oddTile, evenTile, cellTile
from seamwords_cmp import tile_arcs

def colN_list(letters):
    """letters: list of '1','i','-1','-i'. Returns (X, Y, [x at each north step])."""
    x = 0; y = 0; cols = []
    for a in letters:
        if a == '1': x += 1
        elif a == '-1': x -= 1
        elif a == 'i': cols.append(x); y += 1
        elif a == '-i': y -= 1
    return x, y, cols

def arc_letters(s):
    return [t for t in s.split(",") if t]

def strip_width(letters):
    X, Y, cols = colN_list(letters)
    if Y == 0:
        return None
    slope = Fraction(X, Y)
    return max(abs(Fraction(c) - s * slope) for s, c in enumerate(cols))

def main(L):
    dist = {"w1": Counter(), "w2": Counter()}
    bad = []
    n = 0
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w):
            continue
        for child, T in (("odd", oddTile(w)), ("even", evenTile(w))):
            arcs = tile_arcs(cellTile(T))
            if arcs is None:
                continue
            n += 1
            for name, arc in (("w1", arcs[0]), ("w2", arcs[1])):
                d = strip_width(arc_letters(arc))
                if d is None:
                    dist[name]["no_i"] += 1
                    continue
                dist[name][str(d)] += 1
                if d > 1 and len(bad) < 3:
                    bad.append((''.join(map(str, w)), child, name, d))
    print("child tiles:", n)
    for name in ("w1", "w2"):
        print(name, dict(sorted(dist[name].items(), key=lambda kv: kv[0])))
    print("examples with width > 1:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
