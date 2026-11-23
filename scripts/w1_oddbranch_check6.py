"""Task 56 (step 3 check): the full odd-child offers on the conjugate pair, in the odd child's chart (the lead's identity).

Even parent of X: Q_X = (nQ, dQ) = (D - N, D + N). Its field Fq = standard(swap(oddBirthPrefix w)) (checked in check5).
With W = W_w (eps_X = eps_w), lv = (1 - W) U_QX, U_QX = (dQ, nQ), e = V_QX + eps U_QX, V_QX = (nQ - dQ, dQ + nQ),
a(z) = nQ z1 - dQ z2, c = (T_Q - dQ - nQ)/2 + 2W, T_Q = dQ^2 + 2 dQ nQ - nQ^2.
Lead's identity on E_X:  f_X(x) = min( Fq(x - lv), Fq(x - lv - e) + a(x - lv) + c ),  with f_X the odd field quarterTurn(G_w).
Seed check: at seeds z (even, t_X(z) = 1 - d, inside E_X): A(z) = Fq(z - lv), B(z) = Fq(z - lv - e) + a(z - lv) + c, min vs odd.
Also the archive's pure branch values fA = Fq(z - W Up_X), fB_pure = Fq(e - V_X), and the affine piece of B.
Reported over all of E_X (a grid of sites), not just the seed line, to test the identity itself.
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, h0, odd_birth_prefix, swap, parents, win

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 2
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 25

def in_E(n, d, z):
    T = d * d + 2 * d * n - n * n
    L = d + n
    ev = (z[0] + z[1]) % 2 == 0
    a, b, c, h = win(ev, n, d)
    t = n * z[0] - d * z[1]
    s = L * z[0] + (d - n) * z[1]
    return a - T <= t <= b and c <= s <= T + h

def run(w):
    (N, D), (nq, dq) = parents(w)
    eps = N * dq - D * nq
    W = (1 + eps) // 2
    G, _ = standard(tuple(w))
    Fq, _ = standard(tuple(swap(odd_birth_prefix(w))))
    fr = Frame(w)
    d, n = fr.d, fr.n
    nX, dX = (d - n) // 2, (d + n) // 2
    nQ, dQ = D - N, D + N
    UQ = (dQ, nQ)
    VQ = (nQ - dQ, dQ + nQ)
    e = (VQ[0] + eps * UQ[0], VQ[1] + eps * UQ[1])
    TQ = dQ * dQ + 2 * dQ * nQ - nQ * nQ
    c = (TQ - dQ - nQ) // 2 + 2 * W
    lv = ((1 - W) * UQ[0], (1 - W) * UQ[1])
    a = lambda z: nQ * z[0] - dQ * z[1]
    A = lambda x: Fq((x[0] - lv[0], x[1] - lv[1]))
    B = lambda x: Fq((x[0] - lv[0] - e[0], x[1] - lv[1] - e[1])) + a((x[0] - lv[0], x[1] - lv[1])) + c
    odd = lambda z: G((-z[1], z[0] - 1)) + h0(z[0], z[1])
    tX = lambda z: nX * z[0] - dX * z[1]
    B0 = max(abs(nX), abs(dX), 4) * 3 + 8
    grid = [(z1, z2) for z1 in range(-B0, B0 + 1) for z2 in range(-B0, B0 + 1)
            if (z1 + z2) % 2 == 0 and in_E(nX, dX, (z1, z2))]
    ident_bad = [z for z in grid if odd(z) != min(A(z), B(z))]
    seeds = [z for z in grid if tX(z) == 1 - d]
    seed_bad = [z for z in seeds if odd(z) != min(A(z), B(z))]
    seed_vals = [(z, odd(z), A(z), B(z)) for z in seeds]
    return (N, D, nq, dq, eps, W), (nX, dX), len(grid), len(ident_bad), ident_bad[:2], len(seeds), len(seed_bad), seed_vals[:3]

if __name__ == '__main__':
    for L_ in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            fr = Frame(w)
            if fr.d > DMAX:
                continue
            par, X, npts, nbad, ex, nseeds, nsbad, sv = run(w)
            print(''.join(map(str, w)), 'pair', par, 'X', X, 'E_X pts', npts,
                  'identity bad', nbad, ex, 'seeds', nseeds, 'seed bad', nsbad, 'seedvals', sv, flush=True)
