"""Task 66 (2)(c): the s-only separation claim. Windows: even W_e = [0, T+2n], odd W_o = [2-d+n, T+L-2] (even endpoints).
For sc in W(chi_c), si in W(chi_i) (opposite parity), si - sc in {+-L, +-(d-n)}, and x = sc + 2 eps C, y = si + 2 eps C:
claim (x in W_c and y in W_i) or (x - eps T in W_c and y - eps T in W_i). Tested over all such pairs for each word's (n,d,T,C)."""
from chart_threshold_check import params
import sheets as S
words = [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]
for w in words:
    n, d, T, eps, U, sig = params(w)
    fr = S.Frame(list(w)); N, D = fr.N, fr.D
    L = d + n
    C = D * L + N * (d - n)
    We = (0, T + 2 * n); Wo = (2 - d + n, T + L - 2)
    def inW(s, W):
        return W[0] <= s <= W[1]
    bad = 0; tot = 0
    steps = [L, -L, d - n, -(d - n)]
    for chi_c in ("e", "o"):
        Wc, Wi = (We, Wo) if chi_c == "e" else (Wo, We)
        for sc in range(Wc[0] - 2, Wc[1] + 3, 2):
            for st in steps:
                si = sc + st
                if not inW(si, Wi):
                    continue
                tot += 1
                x = sc + 2 * eps * C; y = si + 2 * eps * C
                ok0 = inW(x, Wc) and inW(y, Wi)
                ok1 = inW(x - eps * T, Wc) and inW(y - eps * T, Wi)
                if not (ok0 or ok1):
                    bad += 1
    print(w, "n,d,T,C,eps", (n, d, T, C, eps), "pairs", tot, "bad", bad)
