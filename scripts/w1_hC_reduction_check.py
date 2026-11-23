"""Task 51: the archive's second branch (PAIR_INDUCTION 'Even child branches') with the Lean convention Fp = G o Z + h0.

For every proper word w of length <= MAXLEN (child Frame(w), odd parent (D,N), eps, W):
 z0 = seed point; w0 = z0 - lv - e (the second-branch query), A_aff = a_q.(z0 - lv) + c_e.
 y* = w0 + k Up, Up = 2(D,N) (the odd parent's primary period, zero character: Fp(y+Up) = Fp(y)),
 with k chosen so that sp(y*) = 2 eps - 2N, sp(x) = (D+N) x1 + (D-N) x2 (the archive's sp(y) = 2 eps - 2 np).
 Checks: (a) Fp(y*) = Fp(w0); (b) strip: Fp(y*) = h0(y*) (generic), Fp(y*) = h0(y*) - 1 (W0 exception D - N = 1);
 (c) C(z0) = Fp(y*) + A_aff = 1 (generic), 0 (exception).
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, h0, odd_birth_prefix, swap
MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 3

def run(w):
    fr = Frame(w)
    n, d, L = fr.n, fr.d, fr.L
    N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
    W = (1 + eps) // 2
    Fq, _ = standard(tuple(swap(odd_birth_prefix(w))))
    Fp = lambda x: Fq((-x[1], x[0] - 1)) + h0(*x)
    K = 1 - (D + N) + (1 - W) * eps
    z0 = (eps * (d * K - D * (2 - L)), eps * (n * K - N * (2 - L)))
    lv = ((1 - W) * dq, (1 - W) * nq)
    Vq = (nq - dq, dq + nq)
    e = (Vq[0] + eps * dq, Vq[1] + eps * nq)
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    A_aff = nq * (z0[0] - lv[0]) - dq * (z0[1] - lv[1]) + ce
    w0 = (z0[0] - lv[0] - e[0], z0[1] - lv[1] - e[1])
    Up = (2 * D, 2 * N)
    ks = [k for k in range(-8, 9)
          if (D + N) * (w0[0] + k * Up[0]) + (D - N) * (w0[1] + k * Up[1]) == 2 * eps - 2 * N]
    assert ks, 'no reduction with sp = 2 eps - 2N'
    y = (w0[0] + ks[0] * Up[0], w0[1] + ks[0] * Up[1])
    exc = (eps == -1 and D - N == 1)
    return dict(Fp_eq=(Fp(y) == Fp(w0)), strip=Fp(y) - h0(*y), C=Fp(y) + A_aff, exc=exc)

if __name__ == '__main__':
    bad = []
    cnt = 0
    for L_ in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            r = run(w)
            cnt += 1
            want_strip = -1 if r['exc'] else 0
            want_C = 0 if r['exc'] else 1
            if not (r['Fp_eq'] and r['strip'] == want_strip and r['C'] == want_C):
                bad.append((''.join(map(str, w)), r))
    print('words', cnt, 'failures', len(bad), bad[:3], flush=True)
