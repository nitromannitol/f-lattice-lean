"""Task 74 (field side of odd_zero): for each proper word w with child (n, d), the fixer's seed z (eps, W from the odd parent (D, N),
even (e, r) = (dq, nq)), the line N' z1 - D' z2 = 1 - d with N' = (d - n)/2, D' = (d + n)/2, Y = Z z + U, U = (d, n):
 (a) z on the line, (b) Y in E (closed polygon of w), (c) the sheet values at Y: A(Y) + h0(z) and C(Y) + h0(z) (both expected 0),
 (d) F(Z z) + h0(z) = 0 (the odd seed), and F(Y) = min(A(Y), C(Y)).
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import permit_local as pl  # noqa: E402
import upper_attainment_check as uac  # noqa: E402
import w1_arc_band_check as ab  # noqa: E402
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_sheet_check import h0  # noqa: E402
from exact_quotient import words  # noqa: E402


def main():
    st = Counter()
    for w in words(3):
        P = ab.cc.params(tuple(w))
        eps, N, D, nq, dq, W = P['eps'], P['N'], P['D'], P['nq'], P['dq'], P['W']
        n, d = P['n'], P['d']
        e, r = dq, nq
        Np, Dp = (d - n) // 2, (d + n) // 2
        z = (D + N - 1 + (1 - W) * (e + r), D - N + 1 + (1 - W) * (e - r))
        Zz = (-z[1], z[0] - 1)
        U = (d, n)
        Y = (Zz[0] + U[0], Zz[1] + U[1])
        st[('a: z on line', Np * z[0] - Dp * z[1] == 1 - d)] += 1
        st[('b: Y in E', closed_E(P, Y))] += 1
        lv = ((1 - W) * dq, (1 - W) * nq)
        Vq = (nq - dq, nq + dq)
        ce = (dq * dq + 2 * dq * nq - nq * nq - dq - nq) // 2 + 2 * W
        G, _ = pl.standard(tuple(uac.conjWord(list(w))))
        def Fp(x):
            zx = (-x[1], x[0] - 1)
            return G(zx) - h0(zx)
        a = (Y[0] - lv[0], Y[1] - lv[1])
        c = (a[0] - (Vq[0] + eps * dq), a[1] - (Vq[1] + eps * nq))
        A = Fp(a)
        C = Fp(c) + nq * a[0] - dq * a[1] + ce
        st[('c: A(Y)+h0(z)==0', A + h0(z) == 0)] += 1
        st[('c: C(Y)+h0(z)==0', C + h0(z) == 0)] += 1
        F, _ = pl.standard(tuple(w))
        st[('d: F(Zz)+h0(z)==0', F((-z[1], z[0] - 1)) + h0(z) == 0)] += 1
        st[('F(Y)==min(A,C)', F(Y) == min(A, C))] += 1
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    print('DONE', flush=True)


if __name__ == '__main__':
    main()
