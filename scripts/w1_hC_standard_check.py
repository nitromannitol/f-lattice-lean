"""Task 51 numerics: the second-branch sign hC = (C(z0) >= 0) on the true standard fields (permit_local.standard).

For every proper word w (length <= MAXLEN), with the child Frame(w) (n, d, odd parent (D,N), even parent (dq,nq), eps):
  z0 = the seed point (unique site with t = 2 - L, t_p(z - lv) = 1 - (D+N)), lv = (1-W)(dq,nq), e = Vq + eps Uq;
  A(z0) = Fp(z0 - lv)              (archive: fA = 0, the parent's odd zero)
  C(z0) = Fp(z0 - lv - e) + a_q(z0 - lv) + c_e   (the second branch, hC)
  y = e - Vq = eps Uq               (archive: the reduced parent query, "y = e - Vq in both phases")
  Fp(y)                             and the difference Fp(w) - Fp(y) against h0(w) - h0(y)  (the deck identity)
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from permit_local import standard, Frame, h0, odd_birth_prefix, swap

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 3

def run(w):
    F, _ = standard(tuple(w))
    fr = Frame(w)
    n, d, L, T = fr.n, fr.d, fr.L, fr.T
    N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
    W = (1 + eps) // 2
    wp = odd_birth_prefix(w)
    Fq, _ = standard(tuple(swap(wp)))
    Fp = lambda x: Fq((-x[1], x[0] - 1)) + h0(*x)
    lv = ((1 - W) * dq, (1 - W) * nq)
    Vq = (nq - dq, dq + nq)
    e = (Vq[0] + eps * dq, Vq[1] + eps * nq)
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    K = 1 - (D + N) + (1 - W) * eps
    x0 = eps * (d * K - D * (2 - L))
    y0 = eps * (n * K - N * (2 - L))
    z0 = (x0, y0)
    assert n * x0 - d * y0 == 2 - L and N * (x0 - lv[0]) - D * (y0 - lv[1]) == 1 - (D + N)
    A0 = Fp((x0 - lv[0], y0 - lv[1]))
    w_pt = (x0 - lv[0] - e[0], y0 - lv[1] - e[1])
    C0 = Fp(w_pt) + nq * (x0 - lv[0]) - dq * (y0 - lv[1]) + ce
    y_pt = (eps * dq, eps * nq)
    Fy = Fp(y_pt)
    return dict(n=n, d=d, eps=eps, D=D, N=N, A0=A0, C0=C0, Fw=Fp(w_pt), Fy=Fy,
                hw=h0(*w_pt), hy=h0(*y_pt), inS=(1 - 2 * D <= N * 0 + (D + N) * w_pt[0] + (D - N) * w_pt[1] <= 2 * (D + N) - 1))

if __name__ == '__main__':
    counts = {}
    for L_ in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            r = run(w)
            key = (r['A0'] == 0, r['C0'] >= 0, r['C0'])
            counts[(r['A0'] == 0, r['C0'] if r['C0'] in (0, 1) else ('other' if r['C0'] >= 0 else 'neg'))] = \
                counts.get((r['A0'] == 0, r['C0'] if r['C0'] in (0, 1) else ('other' if r['C0'] >= 0 else 'neg')), 0) + 1
            if r['C0'] < 0 or r['A0'] != 0:
                print('NOTE', ''.join(map(str, w)), r, flush=True)
    print('summary (A0==0, C0 value class): ', counts, flush=True)
