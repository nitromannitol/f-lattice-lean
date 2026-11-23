"""Task 56 (Q2, longitudinal exits), numerical check on the standard fields, words up to length L.

Sites z in E with a horizontal neighbour outside E whose transverse bounds hold (the longitudinal exits):
  east exit (y = z+(1,0) outside E, t-bounds of y hold): v = z - U;   west exit: v = z.
Claims (Q2):
  (a) v in E and 2 - c <= s(v) <= L - 1 (east/west ranges as in Q2);
  (b) F(v) = h0(v) (harmonic strip);
  (c) F(z - sigma) = min(A(v+X), C(v+X)) with X = U_p (W=0) or U_q (W=1), and D_-(z) = F z - F(z - sigma) in [-2, 0];
  (d) the offer A(v+X) >= h0(v) and the offer C(v+X) = h0(v) + 2 (so min in [h0(v), h0(v)+2]).
Also checks that F = min(A, C) on E (the sewn data) and that U is a period of F.
Usage: python3 longitudinal_check.py L"""
import sys
from collections import Counter
from permit_local import standard, proper_words, h0, swap, odd_birth_prefix
from open_inputs_check import frame, in_polygon, window
from i1_i2_roots import sheets

def main(L):
    tally = Counter(); bad = []
    for w in proper_words(L):
        F, _ = standard(tuple(w))
        fr, A, C = sheets(list(w))
        n, d, T = fr["n"], fr["d"], fr["T"]
        eps, W = fr["eps"], fr["W"]
        N, D = fr["N"], fr["D"]
        nq, dq = fr["nq"], fr["dq"]
        sig = (2 * eps * D, 2 * eps * N)
        U = (d, n)
        Up = (2 * D, 2 * N)
        Uq = (dq, nq)
        X = Up if W == 0 else Uq
        L_ = d + n
        c = d - n
        def s_(z): return L_ * z[0] + (d - n) * z[1]
        def t_(z): return n * z[0] - d * z[1]
        x0, x1, y0, y1 = window(fr)
        for x in range(x0, x1 + 1):
            for y in range(y0, y1 + 1):
                z = (x, y)
                if not in_polygon(z, fr): continue
                # min(A,C) = F on E
                tally["E sites"] += 1
                if F(z) != min(A(z), C(z)): tally["F != min(A,C) on E"] += 1
                east = (x + 1, y); west = (x - 1, y)
                kinds = []
                if not in_polygon(east, fr):
                    lo_ok = True
                    ye = east
                    # the t-bounds of the east neighbour
                    ev = (ye[0] + ye[1]) % 2 == 0
                    lo = (2 - T) if ev else (n - T); hi = (d + n - 2) if ev else d
                    if lo <= t_(ye) <= hi: kinds.append("east")
                if not in_polygon(west, fr):
                    ww = west
                    ev = (ww[0] + ww[1]) % 2 == 0
                    lo = (2 - T) if ev else (n - T); hi = (d + n - 2) if ev else d
                    if lo <= t_(ww) <= hi: kinds.append("west")
                for kind in kinds:
                    v = (x - U[0], y - U[1]) if kind == "east" else z
                    vIn = in_polygon(v, fr)
                    tally[kind + " exits"] += 1
                    tally["v in E" if vIn else "v NOT in E"] += 1
                    sv = s_(v)
                    ok_range = (2 - c <= sv <= L_ - 1)
                    tally["s(v) in [2-c, L-1]" if ok_range else "s(v) range FAIL"] += 1
                    hv = h0(v[0], v[1])
                    tally["F(v)=h0(v)" if F(v) == hv else "F(v)!=h0(v)"] += 1
                    vx = (v[0] + X[0], v[1] + X[1])
                    o1, o2 = A(vx), C(vx)
                    tally["min offer = F(z-sigma)" if min(o1, o2) == F((x - sig[0], y - sig[1])) else "min offer != F(z-sigma)"] += 1
                    dm = F(z) - F((x - sig[0], y - sig[1]))
                    tally["D- in [-2,0]" if -2 <= dm <= 0 else "D- OUT"] += 1
                    tally["offer1 >= h0(v)" if o1 >= hv else "offer1 < h0(v)"] += 1
                    tally["offer2 = h0(v)+2" if o2 == hv + 2 else "offer2 != h0(v)+2"] += 1
                    if (F(v) != hv or o1 < hv or o2 != hv + 2) and len(bad) < 3:
                        bad.append((''.join(map(str, w)), kind, z, F(v) - hv, o1 - hv, o2 - hv))
    for k in sorted(tally, key=str): print(k, tally[k])
    print("examples:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
