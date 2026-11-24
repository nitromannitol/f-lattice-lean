"""RankWithIncrements of the W1 policy at 3^k (task 118, W1 base; OldPolicyRanked.rankIncr): exists rank : Site -> Z with lam = 1
(WLOG by scaling), rank(z+U) - rank z = -1, rank(z+V) - rank z = eta (U = kernel (d,1), V = transverse (1-d,1+d), eta = +-1), and
rank i < rank x along every retained edge (x -> i). Difference constraints (totally unimodular), so an LP over a box decides the
truncated system: infeasible on a box is a definitive failure (its constraints are a subset of the full system); feasible on a box
is evidence only. Box = native bounding box enlarged so that z, z+U, z+V all lie in it for many z."""
import sys
import importlib.util
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, 'scripts')
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
PL = load('pl', 'scripts/w1_policy_3k.py')

def feasible(k, eta, margin):
    P = PL.Policy(k); d = P.d
    native = list(P.f.raw)
    xs = [c[0] for c in native]; ys = [c[1] for c in native]
    x0, x1 = min(xs) - margin, max(xs) + margin
    y0, y1 = min(ys) - margin, max(ys) + margin
    U = (d, 1); V = (1 - d, 1 + d)
    sites = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1)]
    idx = {s: n for n, s in enumerate(sites)}
    rows = []; rhs = []; eqrows = []; eqrhs = []
    def inbox(s): return s in idx
    for z in sites:
        zu = (z[0] + U[0], z[1] + U[1])
        if inbox(zu):
            r = np.zeros(len(sites)); r[idx[zu]] = 1; r[idx[z]] = -1
            eqrows.append(r); eqrhs.append(-1)
        zv = (z[0] + V[0], z[1] + V[1])
        if inbox(zv):
            r = np.zeros(len(sites)); r[idx[zv]] = 1; r[idx[z]] = -1
            eqrows.append(r); eqrhs.append(eta)
    nedges = 0
    for x in sites:
        for i in P.R(x):
            if inbox(i):
                r = np.zeros(len(sites)); r[idx[i]] = 1; r[idx[x]] = -1
                rows.append(r); rhs.append(-1); nedges += 1
    A_ub = np.array(rows) if rows else None
    A_eq = np.array(eqrows) if eqrows else None
    res = linprog(np.zeros(len(sites)), A_ub=A_ub, b_ub=np.array(rhs) if rows else None,
                  A_eq=A_eq, b_eq=np.array(eqrhs) if eqrows else None,
                  bounds=[(None, None)] * len(sites), method='simplex')
    return d, len(sites), nedges, res.status, res.message

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or [0, 1, 2]
    for k in ks:
        for eta in (1, -1):
            d, nv, ne, status, msg = feasible(k, eta, margin=2 * (2 * k + 3) // 2 + 2)
            print('rank k=%d d=%d eta=%+d vars %d retained edges %d -> %s (%s)' % (k, d, eta, nv, ne,
                  'FEASIBLE' if status == 0 else ('INFEASIBLE' if status == 2 else 'status %d' % status), msg[:60]), flush=True)
