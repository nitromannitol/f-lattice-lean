"""Strict rank with increments (-1, eta') for the policy e(-1,eta) (task 118, W1 base; lead's request).
R : Z^2 -> Z with R(z+U) - R(z) = -lam, R(z+V) - R(z) = eta' lam (U=(d,1), V=(1-d,1+d)), and R(i) < R(x) along every policy
edge x -> i of e(-1,eta) (the select set of w1_signed_e_3k.py). Lattice Lambda = {z : D | d z2 - z1}, D = d^2+2d-1 (the deck lattice),
with the classes c = (d z2 - z1) mod D and representatives r_c = (-c, 0). Write z = r_c + a U + b V (integers a, b). Then
R(z) = B_c + (-a lam + b eta' lam), B_c free. Strictness becomes the difference constraint
  B_{c(i)} - B_{c(x)} <= -1 - L(i) + L(x),  L(z) = -a lam + b eta' lam.
A negative cycle is an infeasibility certificate (Bellman-Ford on the D classes); its windings are the sums of the displacements i - x
along the cycle (in Lambda, written as a U + b V)."""
import sys
from collections import Counter
sys.path.insert(0, 'scripts')
import importlib.util
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
SE = load('se', 'scripts/w1_signed_e_3k.py')

def coords(d, w):
    D = d * d + 2 * d - 1
    a_num = w[0] * (1 + d) - (1 - d) * w[1]
    b_num = d * w[1] - w[0]
    assert a_num % D == 0 and b_num % D == 0, ('not in lattice', w)
    return a_num // D, b_num // D

def test(k, eta, etap, lam):
    E = SE.E(k); d = E.d; D = d * d + 2 * d - 1
    cls = lambda z: (d * z[1] - z[0]) % D
    rep = lambda c: (-c, 0)
    def L(z):
        c = cls(z); w = (z[0] - rep(c)[0], z[1] - rep(c)[1])
        a, b = coords(d, w)
        return -a * lam + b * etap * lam
    edges = []
    for x in E.native:
        for i in E.select(eta, x):
            edges.append((cls(x), cls(i), -1 - L(i) + L(x), x, i))
    dist = {c: 0 for c in range(D)}
    pred = {}
    last = None
    for it in range(D + 1):
        last = None
        for (u, v, w, x, i) in edges:
            if dist[u] + w < dist[v]:
                dist[v] = dist[u] + w; pred[v] = (u, w, x, i); last = v
        if last is None: break
    if last is None:
        return True, None, len(edges)
    y = last
    for _ in range(D): y = pred[y][0]
    cyc = []; cur = y
    while True:
        u, w, x, i = pred[cur]
        cyc.append((x, i, w))
        cur = u
        if cur == y: break
    cyc.reverse()
    total = sum(w for _, _, w in cyc)
    disp = (sum(i[0] - x[0] for x, i, _ in cyc), sum(i[1] - x[1] for x, i, _ in cyc))
    wa, wb = coords(d, disp) if (disp[0] * 0 == 0) and (d * disp[1] - disp[0]) % D == 0 else (None, None)
    return False, (total, len(cyc), wa, wb, cyc), len(edges)

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or list(range(0, 7))
    for k in ks:
        d = 2 * k + 3
        for eta in (1, -1):
            for etap in (eta, -eta):
                outs = []
                for lam in (1, 2, 3):
                    feas, cert, ne = test(k, eta, etap, lam)
                    outs.append((lam, 'FEASIBLE' if feas else 'INFEASIBLE'))
                    if feas: break
                print('k=%d d=%d policy e(-1,%+d), increments (-1,%+d): %s' % (k, d, eta, etap, outs), flush=True)
                if not feas and cert:
                    total, n, wa, wb, cyc = cert
                    print('    negative cycle: weight %s over %d policy edges, windings (a,b) = (%s,%s) i.e. %s U + %s V' % (total, n, wa, wb, wa, wb))
                    for x, i, w in cyc: print('       ', x, '->', i, ' weight', w)
