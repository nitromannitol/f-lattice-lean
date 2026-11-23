"""Task 55 numerics: the odd-child sheet identity (PAIR_INDUCTION odd child).

For a proper even word w (child n/d, odd parent P_w = (num N, den D), even parent Q_w = (nq, dq), eps, W) and the conjugate
word u = swap(oddBirthPrefix w) (child rotate(P_w) = (D-N, D+N) = Q_X, the even parent of the odd child X = P_X + Q_X, with
P_X = rotate(Q_w)):
  f_w(x) = G_w(Z x) + h0(x)                      (the odd field of w, Z x = (-x2, x1 - 1)),
  Abar(x) = G_u(x - lv), Cbar(x) = G_u(x - lv - e) + a(x - lv) + c,
  lv = (1-W)(dq_X, nq_X), e = V_X + eps U_X, U_X = (D+N, D-N), V_X = (-2N, 2D), a(z) = (D-N) z1 - (D+N) z2,
  c = (T_X - dq_X - nq_X)/2 + 2W, T_X = dq_X^2 + 2 dq_X nq_X - nq_X^2, dq_X = D+N, nq_X = D-N.
Claim tested: f_w(x) = min(Abar(x), Cbar(x)) for all x with Z x in the closed polygon of w (E_w).
Points: y = Z x ranges over the lattice points of E_w (box), x = Z^{-1} y = (y2 + 1, -y1).
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, h0, odd_birth_prefix, swap

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 2
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 25

def in_E(n, d, y):
    L, T = d + n, d * d + 2 * d * n - n * n
    t = n * y[0] - d * y[1]
    s = L * y[0] + (d - n) * y[1]
    if (y[0] + y[1]) % 2 == 0:
        return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
    return n - T <= t <= d and 2 - d + n <= s <= T + d + n - 2

def run(w):
    fr = Frame(w)
    n, d, L, T = fr.n, fr.d, fr.L, fr.T
    N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
    W = (1 + eps) // 2
    Gw, _ = standard(tuple(w))
    Gu, _ = standard(tuple(swap(odd_birth_prefix(w))))
    dX, nX = D + N, D - N
    Lx = (1 - W) * dX, (1 - W) * nX
    VX = (nX - dX, nX + dX)
    UX = (dX, nX)
    e = (VX[0] + eps * UX[0], VX[1] + eps * UX[1])
    TX = dX * dX + 2 * dX * nX - nX * nX
    cX = (TX - dX - nX) // 2 + 2 * W
    a = lambda z: nX * z[0] - dX * z[1]
    Ab = lambda x: Gu((x[0] - Lx[0], x[1] - Lx[1]))
    Cb = lambda x: Gu((x[0] - Lx[0] - e[0], x[1] - Lx[1] - e[1])) + a((x[0] - Lx[0], x[1] - Lx[1])) + cX
    B = T + 2 * (n + d) + 4
    cnt = bad = 0
    ex = []
    kinds = {'min': 0, 'A': 0, 'C': 0, 'other': 0}
    for y1 in range(-B, B + 1):
        for y2 in range(-B, B + 1):
            if not in_E(n, d, (y1, y2)):
                continue
            x = (y2 + 1, -y1)
            fw = Gw((-x[1], x[0] - 1)) + h0(*x)
            A, C = Ab(x), Cb(x)
            cnt += 1
            if fw == min(A, C):
                kinds['min'] += 1
            else:
                bad += 1
                if fw == A: kinds['A'] += 1
                elif fw == C: kinds['C'] += 1
                else: kinds['other'] += 1
                if len(ex) < 3:
                    ex.append((x, fw, A, C))
    return cnt, bad, kinds, ex

if __name__ == '__main__':
    for L_ in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            fr = Frame(w)
            if fr.d > DMAX:
                continue
            cnt, bad, kinds, ex = run(w)
            print(''.join(map(str, w)), 'n,d=', fr.n, fr.d, 'eps=', fr.eps, 'pts', cnt, 'bad', bad, kinds, ex[:2], flush=True)
