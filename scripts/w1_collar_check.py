"""Task 57 numerics: W1_CONSTRUCTOR §3 (free parent roots in an aligned one-pixel collar) and §4 (protected aligned boundary).

Child n/d (even, proper), parents P = (N, D) odd, Q = (nq, dq) even; L = d+n, T = d^2+2dn-n^2, Lp = D+N, Tp = D^2+2DN-N^2,
C = D L + N (d-n), eps = N d - D n = N dq - D nq, W = (1+eps)/2.  Physical grades t = n x - d y, s = L x + (d-n) y.
Parent transform (exact, integral): tp = (C t + eps s)/T, sp = (C s + 2 eps t)/T.
E = closed polygon (Frame.inE); E° = strict interior (b-T < t < a, h < s < T+c, parity-resolved).
H-set = E-points with t >= a(parity) (bottom H arc, t in [a,b]); V-set = E-points with s <= h(parity) (left V arc, s in [c,h]).
Bottom collar = E° points within Chebyshev distance 1 of H-set; left collar = E° points within 1 of V-set.
t* = tp(z - lv), lv = (1-W)(dq,nq) (physical shift); claims: even 1-Lp <= t* <= 0, odd 1-D <= t* <= N.
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import Frame, parents

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 3
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 40

def params(w):
    (N, D), (nq, dq) = parents(w)
    fr = Frame(w)
    n, d = fr.n, fr.d
    L, T = d + n, d * d + 2 * d * n - n * n
    eps = N * dq - D * nq
    assert eps == N * d - D * n
    W = (1 + eps) // 2
    C = D * L + N * (d - n)
    return dict(N=N, D=D, nq=nq, dq=dq, n=n, d=d, L=L, T=T, eps=eps, W=W, C=C, Lp=D + N, Tp=D * D + 2 * D * N - N * N)

def tt(P, z):
    return P['n'] * z[0] - P['d'] * z[1]

def ss(P, z):
    return P['L'] * z[0] + (P['d'] - P['n']) * z[1]

def tp(P, z):
    v = P['C'] * tt(P, z) + P['eps'] * ss(P, z)
    assert v % P['T'] == 0, ('tp not integral', z)
    return v // P['T']

def sp(P, z):
    v = P['C'] * ss(P, z) + 2 * P['eps'] * tt(P, z)
    assert v % P['T'] == 0, ('sp not integral', z)
    return v // P['T']

def bounds(P, ev):
    n, d, L, T = P['n'], P['d'], P['L'], P['T']
    if ev:
        return dict(a=2, b=L - 2, c=0, h=2 * n)
    return dict(a=n, b=d, c=2 - d + n, h=L - 2)

def strict(P, z):
    ev = (z[0] + z[1]) % 2 == 0
    B = bounds(P, ev)
    t, s, T = tt(P, z), ss(P, z), P['T']
    return B['b'] - T < t < B['a'] and B['h'] < s < T + B['c']

def closed(P, z):
    ev = (z[0] + z[1]) % 2 == 0
    B = bounds(P, ev)
    t, s, T = tt(P, z), ss(P, z), P['T']
    return B['b'] - T - (B['a'] - B['b'] + T) * 0 >= 0 or True  # placeholder (see inE)

def in_E(w, z):
    return Frame(w).inE(z)

def run(w):
    P = params(w)
    fr = Frame(w)
    M = 3 * P['d'] + 3
    pts = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if in_E(w, (x, y))]
    Hset = [z for z in pts if tt(P, z) >= bounds(P, (z[0] + z[1]) % 2 == 0)['a']]
    Vset = [z for z in pts if ss(P, z) <= bounds(P, (z[0] + z[1]) % 2 == 0)['h']]
    def near(z, S):
        return any(max(abs(z[0] - h[0]), abs(z[1] - h[1])) <= 1 for h in S)
    bottom = [z for z in pts if strict(P, z) and near(z, Hset)]
    left = [z for z in pts if strict(P, z) and near(z, Vset)]
    lv = ((1 - P['W']) * P['dq'], (1 - P['W']) * P['nq'])
    res = dict(P=P, npts=len(pts), nH=len(Hset), nV=len(Vset))
    # t* on the bottom collar
    tstar = {True: [], False: []}
    for z in bottom:
        ev = (z[0] + z[1]) % 2 == 0
        zz = (z[0] - lv[0], z[1] - lv[1])
        tstar[ev].append(tp(P, zz))
    res['tstar'] = {k: (min(v), max(v), sorted(set(v))) for k, v in tstar.items() if v}
    res['bottom_n'] = len(bottom)
    # s* on the left collar: W1 uses r = z (lv = 0); W0 uses the reflection I - (z - lv)
    sstar_direct = {True: [], False: []}
    sstar_refl = {True: [], False: []}
    for z in left:
        ev = (z[0] + z[1]) % 2 == 0
        zz = (z[0] - lv[0], z[1] - lv[1])
        sstar_direct[ev].append(sp(P, zz))
        q = (1 - zz[0], -1 - zz[1])
        sstar_refl[ev].append(sp(P, q))
    res['sdirect'] = {k: (min(v), max(v), sorted(set(v))) for k, v in sstar_direct.items() if v}
    res['srefl'] = {k: (min(v), max(v), sorted(set(v))) for k, v in sstar_refl.items() if v}
    res['left_n'] = len(left)
    res['Hset_s'] = (min(ss(P, z) for z in Hset), max(ss(P, z) for z in Hset)) if Hset else None
    res['lv_tp'] = tp(P, lv) if lv != (0, 0) else 0
    return res

def check(res):
    P = res['P']
    out = []
    if 'even' is None:
        pass
    ok_t = True
    for ev, (lo, hi, vals) in res['tstar'].items():
        if ev:
            ok_t &= (1 - P['Lp'] <= lo and hi <= 0)
        else:
            ok_t &= (1 - P['D'] <= lo and hi <= P['N'])
    return ok_t

if __name__ == '__main__':
    bad_t = []
    for L_ in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            fr = Frame(w)
            if fr.d > DMAX:
                continue
            res = run(w)
            P = res['P']
            ok = check(res)
            print(''.join(map(str, w)), 'N,D,nq,dq', (P['N'], P['D'], P['nq'], P['dq']), 'n,d', (P['n'], P['d']), 'eps', P['eps'],
                  'W', P['W'], 'lv_tp', res['lv_tp'], '|H|', res['nH'], '|V|', res['nV'],
                  'bottom', res['bottom_n'], 't*', res['tstar'], 'OK_t' if ok else 'FAIL_t',
                  flush=True)
            print('    left', res['left_n'], 'sdirect', res['sdirect'], 'srefl', res['srefl'], 'Hs-range', res['Hset_s'], flush=True)
