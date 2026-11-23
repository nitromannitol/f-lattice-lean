"""Task 57 numerics: the left-collar parent coordinate s* (§2/§3) for both W.
W1 (left, r = z): candidate s* = sp(z - lv) (lv = 0).
W0 (left, r = z): the archive's parent argument for the C offer is y - Vq (y = z - W U = z); candidates:
  c1 = sp(z - Vq), c2 = sp(I - (z - Vq)), c3 = sp(z - lv), c4 = sp(I - (z - lv)).
Claimed ranges: even s* in [2N, 2Lp-2], odd s* in [Lp, 3D+N-2]. sp(p) = (C s(p) + 2 eps t(p))/T (integral, from w1_collar_check).
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
sys.argv = [sys.argv[0], '2', '30']
import importlib.util
spec = importlib.util.spec_from_file_location('cc', '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts/w1_collar_check.py')
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
from permit_local import Frame, parents

def lattice_run(w):
    P = cc.params(w)
    M = 3 * P['d'] + 3
    pts = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if Frame(w).inE((x, y))]
    Vset = [z for z in pts if cc.ss(P, z) <= cc.bounds(P, (z[0] + z[1]) % 2 == 0)['h']]
    def near(z, S):
        return any(max(abs(z[0] - h[0]), abs(z[1] - h[1])) <= 1 for h in S)
    left = [z for z in pts if cc.strict(P, z) and near(z, Vset)]
    return P, left

def V_of(P):
    return (P['nq'] - P['dq'], P['nq'] + P['dq'])

if __name__ == '__main__':
    for L_ in (1, 2):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            if Frame(w).d > 30:
                continue
            P, left = lattice_run(w)
            W = P['W']
            lv = ((1 - W) * P['dq'], (1 - W) * P['nq'])
            Vq = V_of(P)
            I = (1, -1)
            cands = {
                'sp(z-lv)': lambda z: cc.sp(P, (z[0] - lv[0], z[1] - lv[1])),
                'sp(z-Vq)': lambda z: cc.sp(P, (z[0] - Vq[0], z[1] - Vq[1])),
                'sp(I-(z-Vq))': lambda z: cc.sp(P, (I[0] - z[0] + Vq[0], I[1] - z[1] + Vq[1])),
                'sp(I-(z-lv))': lambda z: cc.sp(P, (I[0] - z[0] + lv[0], I[1] - z[1] + lv[1])),
            }
            out = []
            for name, f in cands.items():
                ev = [f(z) for z in left if (z[0] + z[1]) % 2 == 0]
                od = [f(z) for z in left if (z[0] + z[1]) % 2 == 1]
                fits_e = all(2 * P['N'] <= v <= 2 * P['Lp'] - 2 for v in ev) if ev else None
                fits_o = all(P['Lp'] <= v <= 3 * P['D'] + P['N'] - 2 for v in od) if od else None
                out.append((name, (min(ev), max(ev)) if ev else None, fits_e, (min(od), max(od)) if od else None, fits_o))
            print(''.join(map(str, w)), 'W', W, 'N,D,Lp', (P['N'], P['D'], P['Lp']), 'claim even', (2 * P['N'], 2 * P['Lp'] - 2),
                  'odd', (P['Lp'], 3 * P['D'] + P['N'] - 2))
            for row in out:
                print('    ', row, flush=True)
