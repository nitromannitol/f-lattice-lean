"""Task 56 (OddBlackNoRise, numerical check on the standard fields).

For a proper word w (length <= L), F = standard(w) (permit_local.py, the Python model of standardField), sigma = shortShift
= (2 eps D, 2 eps N) with odd parent (N, D) and eps = N*dq - D*nq, D_eta(z) = F(z) - F(z + eta sigma) (eta = 1 here).
OddBlackNoRise: at every site c with laplacian F c = -1 and D(c) odd, both input increments D(i) - D(c) are <= 0.
This script checks this over a box of sites, and also records the configuration counts used by the case analysis:
  (a) black odd centers, (b) rises (an input with D(i) - D(c) = 1), (c) for a rise: the other increment, laplacian at c + sigma.
Usage: python3 oddblack_check.py L R"""
import sys
from collections import Counter
from permit_local import standard, Frame, proper_words, lap

def incN(x):
    return (x[0] - 1, x[1]) if (x[0] + x[1]) % 2 == 0 else (x[0], x[1] - 1)

def incP(x):
    return (x[0] + 1, x[1]) if (x[0] + x[1]) % 2 == 0 else (x[0], x[1] + 1)

def main(L, R):
    tally = Counter(); bad = []
    for w in proper_words(L):
        F, _ = standard(tuple(w))
        fr = Frame(list(w))
        sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
        Dl = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
        tally["words"] += 1
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                c = (x, y)
                if lap(F, c) != -1: continue
                tally["black"] += 1
                if Dl(c) % 2 != 1: continue
                tally["black_odd"] += 1
                for i in (incN(c), incP(c)):
                    inc = Dl(i) - Dl(c)
                    if inc == 1:
                        tally["rise"] += 1
                        other = incP(c) if i == incN(c) else incN(c)
                        o = Dl(other) - Dl(c)
                        tally["rise_other_" + str(o)] += 1
                        cs = (c[0] + sig[0], c[1] + sig[1])
                        tally["rise_translate_black" if lap(F, cs) == -1 else "rise_translate_white"] += 1
                    if inc > 0:
                        if len(bad) < 3: bad.append((w, c, i, inc))
                        tally["VIOLATION"] += 1
    print(dict(tally))
    print("violations:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
