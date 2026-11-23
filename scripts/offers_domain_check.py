"""Task 56 (Q2, the offers on the whole domain): for every v in E with 2 - c <= s(v) <= L - 1 (c = d - n, L = d + n):
  (mem) v + X in E, with X = U_p (W = 0) or U_q (W = 1);
  (first) A(v + X) >= h0(v);
  (second) C(v + X) = h0(v) + 2.
Usage: python3 offers_domain_check.py L"""
import sys
from collections import Counter
from permit_local import proper_words, h0
from open_inputs_check import frame, in_polygon, window
from i1_i2_roots import sheets

def main(L):
    tally = Counter(); bad = []
    for w in proper_words(L):
        fr, A, C = sheets(list(w))
        n, d, T = fr["n"], fr["d"], fr["T"]
        N, D, nq, dq, W = fr["N"], fr["D"], fr["nq"], fr["dq"], fr["W"]
        X = (2 * D, 2 * N) if W == 0 else (dq, nq)
        x0, x1, y0, y1 = window(fr)
        c = d - n; Ls = d + n
        for x in range(x0, x1 + 1):
            for y in range(y0, y1 + 1):
                v = (x, y)
                if not in_polygon(v, fr): continue
                s = (d + n) * x + (d - n) * y
                if not (2 - c <= s <= Ls - 1): continue
                tally["domain"] += 1
                vx = (x + X[0], y + X[1])
                tally["mem" if in_polygon(vx, fr) else "mem FAIL"] += 1
                hv = h0(x, y)
                tally["first" if A(vx) >= hv else "first FAIL"] += 1
                tally["second" if C(vx) == hv + 2 else "second FAIL"] += 1
                if (not in_polygon(vx, fr) or A(vx) < hv or C(vx) != hv + 2) and len(bad) < 3:
                    bad.append((''.join(map(str, w)), v, in_polygon(vx, fr), A(vx) - hv, C(vx) - hv))
    for k in sorted(tally, key=str): print(k, tally[k])
    print("examples:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
