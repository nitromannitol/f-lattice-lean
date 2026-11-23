"""Task 55 (R1, window invariant): do the ordering comparisons of the first pattern hold GLOBALLY on the register tile?

For a phase-0 non-base word w with state (par = (p, q), tO, tE), the register T1 = tO is a point set whose rows are intervals
[lo(c), hi(c)). For every height c1 (both rows nonempty) put c2 = c1 + (d - n) with q = (n, d), and the four ends
  A5 = lo(c1) + (n - d),  B5 = hi(c1) + (n - d),   A4 = lo(c2) + 2d,  B4 = hi(c2) + 2d
(the offsets of pieces 5 and 4 of oddChildB false). The window invariant is: A5 < B5, A4 < B4, A5 <= A4 <= B5 <= B4 for all c1.
This script counts the violations over all c1 (not only the child rows), per word, and reports the minimal slack.
Usage: python3 r1window.py L"""
import sys
from collections import Counter
from standard_tiles import words, state

def row_ends(T):
    rows = {}
    for (x, c) in T:
        rows.setdefault(c, []).append(x)
    out = {}
    for c, xs in rows.items():
        xs = sorted(xs)
        assert xs == list(range(xs[0], xs[-1] + 1)), "row not an interval"
        out[c] = (xs[0], xs[-1] + 1)
    return out

def main(L):
    tally = Counter(); minslack = [None, None, None]; viol = []
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w): continue
        if sum(1 for x in w if x == 1) % 2 == 1: continue   # phase 0 only
        par, tO, tE = state(w)
        p, q = par; n, d = q
        R = row_ends(tO)
        if not R: continue
        lo = lambda c: R[c][0] if c in R else None
        hi = lambda c: R[c][1] if c in R else None
        tally["words"] += 1
        for c1 in range(min(R) - 2 * (n + d) - 3, max(R) + 3):
            c2 = c1 + (d - n)
            if c1 not in R or c2 not in R: continue
            A5, B5 = lo(c1) + (n - d), hi(c1) + (n - d)
            A4, B4 = lo(c2) + 2 * d, hi(c2) + 2 * d
            tally["rows"] += 1
            sl = [A4 - A5, B5 - A4, B4 - B5]
            ok = (A5 < B5) and (A4 < B4) and min(sl) >= 0
            tally["ok" if ok else "viol"] += 1
            for i in range(3):
                if minslack[i] is None or sl[i] < minslack[i][0]:
                    minslack[i] = (sl[i], ''.join(map(str, w)), c1, (n, d))
            if not ok and len(viol) < 3:
                viol.append((''.join(map(str, w)), c1, (n, d), [A5, B5, A4, B4]))
    print(dict(tally))
    print("minimal slacks (A4-A5, B5-A4, B4-B5):", minslack)
    print("violations (first 3):", viol)

if __name__ == "__main__":
    main(int(sys.argv[1]))
