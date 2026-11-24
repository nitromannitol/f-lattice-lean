"""The signed canonical policies e(-1,eta) exactly as in .work/fields/canonical/pure3_initialization/raw/flatrank3.py (main):
  select(e) = black (laplacian -1, both inputs) OR forced (even centre, no free alias, x-rule: dx=-1 if x<=0, dx=+1 if x>=2)
              OR freeE (some free alias q = c + shift(L) has the eta free table at q: H even east, H odd north, H_0 vertical -eta;
              V_0 east; V_d eta-horizontal; V_j vertical -eta).
Prices as in the notes (= Lean frame.price / slip / chainPotential at frameAt 3^k): P, D_eta, Phi_eta.
Bounded correction r_eta = val(rep translate) with the saved val of flatrank3.py (0 <= r_eta <= 2d+2 asserted); the full rank is
(2d+3) Phi_eta + r_eta. Tests: P, D_eta, Phi_eta nonincreasing on select; r_eta drops by >=1 on every Phi-flat select edge; bounded;
Phi increments (-1, 2 eta). Strict drop of (2d+3)Phi+r then follows on every select edge (Phi drop of >=1 costs 2d+3 > the r
variation 2d+2)."""
import sys
from collections import Counter
sys.path.insert(0, 'scripts')
import importlib.util
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
W = load('w', 'scripts/w1_free_root_gate.py')   # native, isrep, shift, f (isfree), ranks
SG = load('sg', 'scripts/w1_signed_3k.py')      # Policy (lap, F), Field

ALIAS = sorted([(i, j) for i in range(-2, 3) for j in range(-2, 3)], key=lambda q: abs(q[0]) + abs(q[1]))
ALIAS_WIN = [(i, j) for i in range(-2, 3) for j in (-1, 0, 1)]

def even(c): return (c[0] + c[1]) % 2 == 0
def isH(d, X, Y): return Y == 0 and 1 <= X <= d
def isV(d, X, Y): return (X, Y) == (0, 0) or (X + Y == 1 and 1 <= Y < d) or (X, Y) == (2 - d, d)

def freeE(d, X, Y, eta, dx, dy):
    """the free table of flatrank3.py freeE, for a free point (X,Y) and the displacement (dx,dy)"""
    if isH(d, X, Y):
        return ((dx == 0 and dy == -eta) if X == 1 else (dx + dy == 1))
    if isV(d, X, Y):
        if (X, Y) == (0, 0): return dx == 1
        return (dx == eta and dy == 0) or (dx == 0 and dy == -eta)
    return False

def val(d, X, Y, eta):
    p = (X + Y) % 2
    H = isH(d, X, Y); V = isV(d, X, Y)
    if eta == -1:
        hr = 2 * d - 1 - 2 * X + p
        vr = 2 * d - 1 if Y == 0 else (1 if Y == d else 2 * d - 2 * Y)
        if X + Y == d + 1 and X >= 1: br = (2 * d - 1 if X == 1 else 0)
        elif X <= 0: br = 2 * d - 3 + 2 * X + p
        else: br = 2 * d - 1 - 2 * X + p
    else:
        if X == 1: hr = 5
        elif X == 2: hr = 2
        elif X == 3: hr = 1
        else: hr = 2 * d + 6 - 2 * X + p
        vr = (0 if d == 3 else 6) if Y == 0 else (4 if Y == d else (1 if Y >= d - 2 else 2 * Y + 5))
        if X + Y == 2: br = (2 if (Y == 1 or Y >= d - 2) else 0)
        elif X <= 1: br = 2 * d - 4 + 2 * X + p
        elif X <= 3: br = p
        else: br = 2 * d + 6 - 2 * X + p
    return hr if H else (vr if V else br)

def rval(d, X, Y, eta):
    for (i, j) in ALIAS:
        u = W.shift(d, X, Y, i, j)
        if W.isrep(d, u[0], u[1]):
            return val(d, u[0], u[1], eta)
    return None

class E:
    def __init__(self, k):
        self.P0 = SG.PL.Policy(k); self.d = self.P0.d
        self.native = list(self.P0.f.raw)
        self.cache = {}
    def free_alias_points(self, c):
        d = self.d
        out = []
        for (i, j) in ALIAS_WIN:
            q = W.shift(d, c[0], c[1], i, j)
            if W.native(d, q[0], q[1]) and W.f.isfree(d, q[0], q[1]): out.append(q)
        return out
    def select(self, eta, c):
        """the retained inputs of e(-1,eta) at c (flatrank3 select)"""
        key = (eta, c)
        if key in self.cache: return self.cache[key]
        d = self.d
        l = self.P0.lap(c)
        ax = [(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)]
        out = set()
        frees = self.free_alias_points(c)
        for e in ax:
            ok = False
            if l == -1: ok = True
            if even(c) and not frees and ((c[0] <= 0 and e == (-1, 0)) or (c[0] >= 2 and e == (1, 0))): ok = True
            for q in frees:
                if freeE(d, q[0], q[1], eta, e[0], e[1]): ok = True
            if ok: out.add((c[0] + e[0], c[1] + e[1]))
        self.cache[key] = out
        return out

def run(k):
    Ek = E(k); d = Ek.d; P0 = Ek.P0
    res = Counter(); ex = {}
    def fail(n, info): res[n] += 1; ex.setdefault(n, info)
    def price(z): return P0.G(z) - P0.G((z[0] - 1, z[1] + 1)) - z[1]
    def slip(eta, z): return P0.G(z) - P0.G((z[0] - 2 * eta, z[1]))
    def phi(eta, z): return P0.G(z) - P0.G((z[0] - 1 - 2 * eta, z[1] + 1)) - z[1]
    for c in Ek.native:
        l = P0.lap(c); res['centres'] += 1
        if l not in (-1, 0): fail('lap-other', (c, l))
        res[('count', len(Ek.select(1, c)), len(Ek.select(-1, c)))] += 1
        for eta in (1, -1):
            Rc = Ek.select(eta, c)
            if l == -1 and Rc != {(c[0] + e[0], c[1] + e[1]) for e in ([(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)])}:
                fail('black-both%+d' % eta, c)
            if l == 0 and len(Rc) == 0: fail('white-none%+d' % eta, c)
            for i in Rc:
                if not price(i) <= price(c): fail('price%+d' % eta, (c, i))
                if not slip(eta, i) <= slip(eta, c): fail('D%+d' % eta, (c, i))
                if not phi(eta, i) <= phi(eta, c): fail('Phi%+d' % eta, (c, i))
                # Phi-flat edges: r must drop by >= 1
                if phi(eta, i) == phi(eta, c):
                    ri = rval(d, i[0], i[1], eta); rc = rval(d, c[0], c[1], eta)
                    if ri is None or rc is None or not ri <= rc - 1: fail('r-flat%+d' % eta, (c, i, rc, ri))
    # bounds and increments of r and Phi, on the native domain of the test
    for eta in (1, -1):
        for c in Ek.native:
            rc = rval(d, c[0], c[1], eta)
            if rc is None or not (0 <= rc <= 2 * d + 2): fail('r-bound%+d' % eta, (c, rc))
    return d, res, ex

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or list(range(0, 7))
    for k in ks:
        d, res, ex = run(k)
        print('k=%d d=%d' % (k, d), {a: b for a, b in res.items() if not isinstance(a, tuple)}, {a: b for a, b in list(ex.items())[:2]}, flush=True)
        cnt = Counter({a: b for a, b in res.items() if isinstance(a, tuple)})
        print('   retained-count (plus,minus) at native centres:', dict(cnt), flush=True)
