"""Task 61 numerics: the §3 inward core squares of the bottom and left collars (W1_CONSTRUCTOR §3).

Strict white collar roots (within Chebyshev one of the H arc, bottom; of the V arc, left) of the child field F = standard(u).
For a bottom root z the archive uses the upper-left unit square {z, z-(1,0), z+(0,1), z+(-1,1)} (corners strictly inside E° and
containing z); the test counts roots whose upper-left square lies in E° (strict), for each of the four squares containing z.
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
import importlib.util
_sv = sys.argv; sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts/w1_collar_check.py')
cc = importlib.util.module_from_spec(spec); spec.loader.exec_module(cc)
sys.argv = _sv
from permit_local import Frame, parents
from w1_forcing_check import inn, inp, lap, standard

def squares_containing(z):
    out = []
    for a in (z[0] - 1, z[0]):
        for b in (z[1] - 1, z[1]):
            out.append((a, b, [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]))
    return out

def test(u):
    P = cc.params(u)
    G, _ = standard(tuple(u))
    M = 3 * P['d'] + 3
    E0 = set((x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.strict(P, (x, y)))
    Hset = []
    Vset = []
    allpts = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if Frame(list(u)).inE((x, y))]
    for z in allpts:
        ev = (z[0] + z[1]) % 2 == 0
        if cc.tt(P, z) >= cc.bounds(P, ev)['a']:
            Hset.append(z)
        if cc.ss(P, z) <= cc.bounds(P, ev)['h']:
            Vset.append(z)
    Hs = set(Hset)
    Vs = set(Vset)
    def near(z, S):
        return any(max(abs(z[0] - h[0]), abs(z[1] - h[1])) <= 1 for h in S)
    bottom = [z for z in E0 if lap(G, z) == 0 and near(z, Hs)]
    res = {'bottom roots': len(bottom), 'upper-left strict': 0, 'any square strict': 0, 'no strict square': []}
    for z in bottom:
        ul = [z, (z[0] - 1, z[1]), (z[0], z[1] + 1), (z[0] - 1, z[1] + 1)]
        if all(q in E0 for q in ul):
            res['upper-left strict'] += 1
        ok_any = False
        for a, b, corners in squares_containing(z):
            if all(q in E0 for q in corners):
                ok_any = True
                break
        if ok_any:
            res['any square strict'] += 1
        else:
            res['no strict square'].append(z)
    res['no strict square'] = res['no strict square'][:3]
    return res

if __name__ == '__main__':
    for L_ in (1, 2, 3):
        for u in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in u) or all(x == 2 for x in u):
                continue
            print(''.join(map(str, u)), test(u), flush=True)
