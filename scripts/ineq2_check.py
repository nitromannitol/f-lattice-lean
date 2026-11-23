"""Task 56 (Q2 input (2), Q4-strips.md), numerical check.

f = Fp (permit_local.py): f(x) = h0(x) + G(Z x), Z(x,y) = (-y, x-1), G = standard(swap(oddBirthPrefix w)) = the earlier conjugate,
equivalently f(x,y) = h0(x,y) + g(r - s_p(x,y)) with s_p = r x + b y, r = D+N, b = D-N, t_p = N x - D y (Q4-strips.md).
f_chi(k) = f at transverse coordinate k = t_p(x) and parity chi of x (Q4: well defined, equal k and chi differ by U_p).
Statement (2): d_f(k, chi) = f_chi(k) - f_chi(k-1) satisfies d_f >= 0 for k < N and d_f <= 0 for k >= N.
This script (a) checks that f_chi(k) depends only on (k, chi) over a box, and (b) checks the sign pattern (2).
Usage: python3 ineq2_check.py L R"""
import sys
from collections import Counter
from permit_local import standard, parents, h0, swap, odd_birth_prefix, proper_words, Frame

def main(L, R):
    tally = Counter(); bad = []
    for w in proper_words(L):
        Fq, _ = standard(tuple(swap(odd_birth_prefix(list(w)))))
        fr = Frame(list(w))
        N, D = fr.N, fr.D
        f = lambda x: h0(x[0], x[1]) + Fq((-x[1], x[0] - 1))
        val = {}
        ok = True
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                chi = (x + y) % 2
                k = N * x - D * y
                v = f((x, y))
                key = (chi, k)
                if key in val and val[key] != v:
                    ok = False
                    if len(bad) < 3: bad.append(("not well defined", ''.join(map(str, w)), key, val[key], v))
                val.setdefault(key, v)
        tally["words"] += 1
        tally["well_defined" if ok else "NOT well defined"] += 1
        for (chi, k), v in list(val.items()):
            if (chi, k - 1) not in val: continue
            dfk = v - val[(chi, k - 1)]
            if k < N:
                tally["k<N: d_f>=0" if dfk >= 0 else "k<N VIOLATION"] += 1
                if dfk < 0 and len(bad) < 3: bad.append(("k<N", ''.join(map(str, w)), chi, k, dfk))
            else:
                tally["k>=N: d_f<=0" if dfk <= 0 else "k>=N VIOLATION"] += 1
                if dfk > 0 and len(bad) < 3: bad.append(("k>=N", ''.join(map(str, w)), chi, k, dfk))
    print(dict(tally))
    print("failures:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
