"""Task 55 (R1, ii): the right boundary of a register tile lies in a strip around its chord.

For a register tile P (odd or even, register states of words up to length L), its boundary loop from (0,0) is the four-arc
loop w1 w2 (-w1) (-w2) (seamwords_cmp.tile_arcs). Let U = w1 ++ w2 with endpoint (S, H) = (sum U). The right row ends are
FF(c) = colN(U, c) for 0 <= c < H (north steps of U). Measure D = max_c |FF(c) - c*S/H| and the window sums:
  W(e, d) = max over windows of |(FF(e+d) - FF(e)) - d*S/H|.
Usage: python3 r1chordU.py L"""
import sys
from collections import Counter
from fractions import Fraction
from standard_tiles import words, state, cellTile
from seamwords_cmp import tile_arcs
from r1arcstrip import colN_list, arc_letters

def right_row_ends(letters):
    X, Y, cols = colN_list(letters)
    return X, Y, cols

def main(L):
    dist = Counter(); worst = []
    n = 0
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w): continue
        par, tO, tE = state(w)
        for name, T in (("odd", tO), ("even", tE)):
            arcs = tile_arcs(cellTile(T))
            if arcs is None: continue
            l1 = arc_letters(arcs[0]); l2 = arc_letters(arcs[1])
            X, Y, cols = colN_list(l1 + l2)
            if Y == 0: continue
            n += 1
            slope = Fraction(X, Y)
            D = max(abs(Fraction(cols[c]) - c * slope) for c in range(Y))
            dist[str(D) if D.denominator == 1 else "frac"] += 1
            if D > 2 and len(worst) < 3:
                worst.append((''.join(map(str, w)), name, str(D), X, Y))
    print("tiles", n)
    print("max deviation of FF from its chord, by value:", sorted(dist.items(), key=lambda kv: kv[0]))
    print("examples with deviation > 2:", worst)

if __name__ == "__main__":
    main(int(sys.argv[1]))
