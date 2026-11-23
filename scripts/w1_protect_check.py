"""Task 57 numerics: W1_CONSTRUCTOR §4 (protected aligned boundary, arithmetic of the native endpoints).

Even native H endpoints (2l-b, b), b = floor(2 n l / L), 1 <= l <= L/2 - 1: claim tp = r (residue of 2Nl mod Lp), except
r = 0 with eps = +1, where tp = Lp.
Odd native V endpoints (-b, 2l-1-b), b = floor((d-n) l / d), 1 <= l <= d-1: f = (D-N) l - D b; claim f = residue of (D-N) l mod D,
except residue 0 with eps = -1 where f = D; relevant parent sp (left collar s*) = sp(z - (1-W) Vq) =? 2f - (D-N) - 2(1-W).
Also the H-set tp values (named extreme H_last: tp = D + eps, odd).
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
sys.argv = [sys.argv[0], '2', '30']
import importlib.util
spec = importlib.util.spec_from_file_location('cc', '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts/w1_collar_check.py')
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
from permit_local import Frame, parents

def H_endpoint_check(w):
    P = cc.params(w)
    N, D, Lp, L, n, d, eps = P['N'], P['D'], P['Lp'], P['L'], P['n'], P['d'], P['eps']
    bad = []
    rows = []
    for l in range(1, L // 2):          # 1 <= l <= L/2 - 1 (L even for even child)
        b = (2 * n * l) // L
        z = (2 * l - b, b)
        r = (2 * N * l) % Lp
        pred = Lp if (r == 0 and eps == 1) else r
        tpz = cc.tp(P, z)
        ok = (tpz == pred) and (cc.tt(P, z) >= 2) and (cc.tt(P, z) <= L - 2)
        if not ok:
            bad.append((l, z, tpz, pred))
        rows.append((l, z, tpz))
    return bad, rows

def odd_V_check(w):
    P = cc.params(w)
    N, D, Lp, L, n, d, eps, W = P['N'], P['D'], P['Lp'], P['L'], P['n'], P['d'], P['eps'], P['W']
    Vq = (P['nq'] - P['dq'], P['nq'] + P['dq'])
    bad = []
    rows = []
    for l in range(1, d):
        b = ((d - n) * l) // d
        z = (-b, 2 * l - 1 - b)
        f = (D - N) * l - D * b
        r0 = ((D - N) * l) % D
        pred = D if (r0 == 0 and eps == -1) else r0
        okf = (f == pred)
        sp_rel = cc.sp(P, (z[0] - (1 - W) * Vq[0], z[1] - (1 - W) * Vq[1]))
        claim_sp = 2 * f - (D - N) - 2 * (1 - W)
        if not okf or sp_rel != claim_sp:
            bad.append((l, z, f, pred, sp_rel, claim_sp))
        rows.append((l, z, f, sp_rel))
    return bad, rows

def H_tp_values(w):
    P = cc.params(w)
    M = 3 * P['d'] + 3
    pts = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if Frame(w).inE((x, y))]
    Hset = [z for z in pts if cc.tt(P, z) >= cc.bounds(P, (z[0] + z[1]) % 2 == 0)['a']]
    ev = sorted(set(cc.tp(P, z) for z in Hset if (z[0] + z[1]) % 2 == 0))
    od = sorted(set(cc.tp(P, z) for z in Hset if (z[0] + z[1]) % 2 == 1))
    return ev, od

if __name__ == '__main__':
    for L_ in (1, 2):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            if Frame(w).d > 30:
                continue
            P = cc.params(w)
            badH, rowsH = H_endpoint_check(w)
            badV, rowsV = odd_V_check(w)
            ev, od = H_tp_values(w)
            print(''.join(map(str, w)), 'N,D,Lp', (P['N'], P['D'], P['Lp']), 'eps', P['eps'], 'W', P['W'],
                  'H-endpoints bad', len(badH), badH[:2], '| V-endpoints bad', len(badV), badV[:2],
                  '| H-set tp even', ev, 'odd', od, 'D+eps', P['D'] + P['eps'], flush=True)
