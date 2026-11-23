"""Task 56 (Q2, V-arc range), numerical check on the standard fields.

Lean: VArcInputs.leftRange: for every z with OnVArc E z (z in E and a horizontal neighbour z +- (1,0) outside E),
starDiff F sigma z in {0,1,2}, where starDiff F sigma z = F z - F (z + sigma) and sigma = shortShift
= (2 eps D, 2 eps N) (odd parent (N, D), eps = N dq - nq D).
Q2 (fixes/Q2.md) proves D_- = F z - F (z - sigma) in [-2, 0] at those sites; reflection gives the positive range.
This script checks both on all proper words up to length L, over the window of E.
Usage: python3 varc_check.py L"""
import sys
from collections import Counter
from permit_local import standard, proper_words
from open_inputs_check import frame, in_polygon, window

def main(L):
    tally = Counter(); bad = []
    for w in proper_words(L):
        F, _ = standard(tuple(w))
        fr = frame(list(w))
        sig = (2 * fr["eps"] * fr["D"], 2 * fr["eps"] * fr["N"])
        x0, x1, y0, y1 = window(fr)
        tally["words"] += 1
        for x in range(x0, x1 + 1):
            for y in range(y0, y1 + 1):
                z = (x, y)
                if not in_polygon(z, fr): continue
                outside_h = (not in_polygon((x - 1, y), fr)) or (not in_polygon((x + 1, y), fr))
                if not outside_h: continue
                tally["varc"] += 1
                dp = F(z) - F((x + sig[0], y + sig[1]))
                dm = F(z) - F((x - sig[0], y - sig[1]))
                tally["D+ in {0,1,2}" if dp in (0, 1, 2) else "D+ OUT"] += 1
                tally["D- in [-2,0]" if -2 <= dm <= 0 else "D- OUT"] += 1
                if dp not in (0, 1, 2) and len(bad) < 3:
                    bad.append(("D+", ''.join(map(str, w)), z, dp))
                if not (-2 <= dm <= 0) and len(bad) < 3:
                    bad.append(("D-", ''.join(map(str, w)), z, dm))
    print(dict(tally))
    print("failures:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
