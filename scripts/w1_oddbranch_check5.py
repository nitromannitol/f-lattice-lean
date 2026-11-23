"""Task 56 (step 2, correct odd child): the archive's odd-child branches for the conjugate pair.

The odd child of w is X = P_X + Q_X with P_X = rotate(Q_w) (odd parent), Q_X = rotate(P_w) (even parent): the Farey relation
of W1Oddchild. In numerators/denominators (num, den):
  P_X = ((dq - nq)/2, (dq + nq)/2),  Q_X = (D - N, D + N),  X = ((d - n)/2, (d + n)/2), with d = 2D+dq, n = 2N+nq.
  eps_X = Nx dQ - Dx nQ = dq N - nq D = eps_w (checked), so W_X = W.
Field of Q_X: Fq = standard(swap(oddBirthPrefix w)) (child Q_X = rotate(P_w); seed t_Q = 2 - dQ - nQ = 2 - 2D).
Odd field: F_X(z) = quarterTurn(G_w)(z) = G_w(Zz) + h0(z).
Seed (archive): even z with t_X(z) = 1 - d, t_X(z) = n_X z1 - d_X z2 (n_X=(d-n)/2, d_X=(d+n)/2); z = b + e, b = (1-W) Up_X + Uq_X.
Branch A: x = z - W Up_X, Up_X = 2 P_X = (dq + nq, dq - nq) (site as (den, num)); fA = Fq(x); seed t_Q(x) = 2 - 2D.
Branch B: y = e - V_X, V_X = (N_X - D_X, N_X + D_X) = (-nq, dq); fB = Fq(y); seed s_Q(y) = -2 eps - 2 nQ = -2 eps - 2(D-N).
Polygon test: z in closed polygon of the pair-child X' (window rule with (n_X, d_X)); also reported without restriction.
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
    wp = swap(odd_birth_prefix(w))
    Fq, _ = standard(tuple(wp))
    fr = Frame(w)
    d, n = fr.d, fr.n
    nX, dX = (d - n) // 2, (d + n) // 2
    NX, DX = (dq - nq) // 2, (dq + nq) // 2
    nQX, dQX = D - N, D + N
    assert (nQX, dQX) == (Frame(wp).n, Frame(wp).d), (w, nQX, dQX, Frame(wp).n, Frame(wp).d)
    assert NX * dQX - DX * nQX == eps, (w,)
    tX = lambda z: nX * z[0] - dX * z[1]
    target = 1 - d
    UpX = (dq + nq, dq - nq)
    VX = (-nq, dq)
    e = (-1, 1)
    tQ = lambda x: nQX * x[0] - dQX * x[1]
    sQ = lambda y: (dQX + nQX) * y[0] + (dQX - nQX) * y[1]
    B = 3 * d + 10
    rows = []
    for z1 in range(-B, B + 1):
        for z2 in range(-B, B + 1):
            z = (z1, z2)
            if (z1 + z2) % 2 != 0 or tX(z) != target:
                continue
            odd = G((-z2, z1 - 1)) + h0(z1, z2)
            xA = (z1 - W * UpX[0], z2 - W * UpX[1])
            fA = Fq(xA)
            y = (e[0] - VX[0], e[1] - VX[1])
            fB = Fq(y)
            rows.append(dict(z=z, odd=odd, fA=fA, tA=tQ(xA), fB=fB, sB=sQ(y), h0y=h0(*y), inE=in_E(nX, dX, z), inW=Frame(w).inE(z)))
    return dict(pair=(N, D, nq, dq, eps, W), X=(nX, dX), QX=(nQX, dQX), rows=rows)

if __name__ == '__main__':
    for L_ in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            fr = Frame(w)
            if fr.d > DMAX:
                continue
            res = run(w)
            rows = res['rows']
            inE = [r for r in rows if r['inE']]
            print(''.join(map(str, w)), 'pair', res['pair'], 'X', res['X'], 'QX', res['QX'],
                  'seeds', len(rows), 'inEX', len(inE),
                  'inEX: odd!=0', sum(r['odd'] != 0 for r in inE), 'fA!=0', sum(r['fA'] != 0 for r in inE),
                  'tA!=seed', sum(r['tA'] != 2 - 2 * res['pair'][1] for r in inE),
                  'fB!=0', sum(r['fB'] != 0 for r in inE),
                  'sB!=seed', sum(r['sB'] != -2 * res['pair'][4] - 2 * (res['pair'][1] - res['pair'][0]) for r in inE), flush=True)
            for r in inE[:3]:
                print('   z', r['z'], 'odd', r['odd'], 'fA', r['fA'], 'tA', r['tA'], 'fB', r['fB'], 'sB', r['sB'], 'h0y', r['h0y'], flush=True)
