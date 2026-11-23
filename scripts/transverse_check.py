"""Task 56 (Q2, transverse exits), numerical check on the standard fields, words up to length L.

For z in E (in_polygon) with a horizontal neighbour outside E:
  EastUpper: y = z + (1,0) fails its upper t-bound (t(y) > upper bound of y's parity)  -> claim D_-(z) = 0;
  WestLower: w = z - (1,0) fails its lower t-bound (t(w) < lower bound of w's parity)  -> claim D_-(z) = -2;
  impossible: east lower t-failure, west upper t-failure (checked: must never occur);
  otherwise the failure is longitudinal (s-bound), not covered here.
D_-(z) = F z - F(z - sigma), sigma = shortShift. t = n x - d y; t(V) = -T with V = child transverse.
Usage: python3 transverse_check.py L"""
import sys
from collections import Counter
from permit_local import standard, proper_words
from open_inputs_check import frame, in_polygon, window, even_site

def t_bounds(z, fr):
    n, d, T = fr["n"], fr["d"], fr["T"]
    t = n * z[0] - d * z[1]
    if even_site(z): return 2 - T, d + n - 2, t
    return n - T, d, t

def main(L):
    tally = Counter(); bad = []
    for w in proper_words(L):
        F, _ = standard(tuple(w))
        fr = frame(list(w))
        sig = (2 * fr["eps"] * fr["D"], 2 * fr["eps"] * fr["N"])
        x0, x1, y0, y1 = window(fr)
        for x in range(x0, x1 + 1):
            for y in range(y0, y1 + 1):
                z = (x, y)
                if not in_polygon(z, fr): continue
                Dm = F(z) - F((x - sig[0], y - sig[1]))
                east = (x + 1, y); west = (x - 1, y)
                if not in_polygon(east, fr):
                    lo, hi, t = t_bounds(east, fr)
                    if t > hi:
                        tally["EastUpper"] += 1
                        tally["EastUpper: D- = 0" if Dm == 0 else "EastUpper VIOLATION"] += 1
                        if Dm != 0 and len(bad) < 3: bad.append(("EU", ''.join(map(str, w)), z, Dm))
                    elif t < lo:
                        tally["EastLower (impossible)"] += 1
                        bad.append(("EL", ''.join(map(str, w)), z))
                if not in_polygon(west, fr):
                    lo, hi, t = t_bounds(west, fr)
                    if t < lo:
                        tally["WestLower"] += 1
                        tally["WestLower: D- = -2" if Dm == -2 else "WestLower VIOLATION"] += 1
                        if Dm != -2 and len(bad) < 3: bad.append(("WL", ''.join(map(str, w)), z, Dm))
                    elif t > hi:
                        tally["WestUpper (impossible)"] += 1
                        bad.append(("WU", ''.join(map(str, w)), z))
    print(dict(tally))
    print("failures:", bad[:3])

if __name__ == "__main__":
    main(int(sys.argv[1]))
