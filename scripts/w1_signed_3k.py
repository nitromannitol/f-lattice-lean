"""Signed canonical policies e(-1,eta) at 3^k (from the notes
.work/fields/canonical/pure3_initialization/raw/UNIFORM_RECIPROCAL_RAW_PRICE_PROOF.md and clean/CLEAN_PHYSICAL_BAND_AND_ALL_THRESHOLD_BINARY.md).
Prices (convention check against Lean frame.price / slip / chainPotential at frameAt 3^k, eps = -1):
  P(z) = F(z) - F(z+(-1,1)) - y ;  D_eta(z) = F(z) - F(z+(-2 eta,0)) ;  Phi_eta(z) = F(z) - F(z+(-1-2 eta,1)) - y.
Policy e_eta on the native centres:
  black (laplacian -1): both parity-axis inputs;
  free centre (native H_j or V_j, V_0, V_d): the note's table: H_j even east, H_j odd north, except H_0 = (1,0) vertical -eta;
     V_0 = (0,0) east; V_j (1<=j<d, odd) vertical -eta; V_d = (2-d,d) eta-horizontal;
  nonfree even white: west if x <= 0, east if x >= 2 (matches every forced arrow, checked);
  nonfree odd white (not covered by the notes read): the lower-rank retained input, retained set and rank = plus for eta=+1, minus for eta=-1.
Tests: quota, P / D_eta / Phi_eta nonincreasing along e_eta, the free table inside its retained set, and the rank R_eta = Phi_eta + r
with r periodic on the deck (difference constraints on the D classes; g(z) = d z2 - z1 mod D), and the increments Phi(z+U)-Phi(z)=-1,
Phi(z+V)-Phi(z)=2 eta."""
import sys
from collections import Counter
sys.path.insert(0, 'scripts')
import importlib.util
from fractions import Fraction as Fr
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
PL = load('pl', 'scripts/w1_policy_3k.py')
PLUS = load('plus', 'scripts/w1_plus_gate.py')

def even(c): return (c[0] + c[1]) % 2 == 0
def add(p, e): return (p[0] + e[0], p[1] + e[1])

class Signed:
    def __init__(self, k):
        self.P0 = PL.Policy(k); self.d = self.P0.d; self.f = self.P0.f; self.Fc = self.P0.Fc
        self.native = list(self.f.raw); self.nset = set(self.native)
        self.cache = {}
    def G(self, z): return self.P0.G(z)
    def price(self, z): return self.G(z) - self.G((z[0] - 1, z[1] + 1)) - z[1]
    def slip(self, eta, z): return self.G(z) - self.G((z[0] - 2 * eta, z[1]))
    def phi(self, eta, z): return self.G(z) - self.G((z[0] - 1 - 2 * eta, z[1] + 1)) - z[1]
    def free_table(self, eta, c):
        """the note's free table as a displacement (unit step) from the free centre c"""
        d = self.d
        if c[1] == 0 and 1 <= c[0] <= d:               # H_j
            if c[0] % 2 == 0: return (1, 0)            # even: east
            if c == (1, 0): return (0, -eta)           # H_0 vertical -eta
            return (0, 1)                              # odd: north
        if c == (0, 0): return (1, 0)                  # V_0 east
        if c == (2 - d, d): return (eta, 0)            # V_d eta-horizontal
        return (0, -eta)                               # V_j odd: vertical -eta
    def retained_for_sign(self, eta, c):
        if eta == 1:
            return self.P0.retained_minus(c) if False else None
    def candidates(self, eta, c):
        """retained parity-axis unit inputs of the sign's rule: plus for eta=+1, minus for eta=-1"""
        ax = [(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)]
        if eta == 1:
            return [e for e in ax if PLUS.edgePlus(self.d, c[0], c[1], e[0], e[1])]
        return [e for e in ax if e in self.P0.retained_minus(c)]
    def R(self, eta, c):
        key = (eta, c)
        if key in self.cache: return self.cache[key]
        lap = self.P0.lap(c)
        ax_in = [add(c, e) for e in ([(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)])]
        if lap == -1:
            out = set(ax_in)
        elif lap == 0:
            if self.P0.free(c):
                out = {add(c, self.free_table(eta, c))}
            elif even(c):
                out = {add(c, (-1, 0))} if c[0] <= 0 else {add(c, (1, 0))}
            else:
                cand = [e for e in self.candidates(eta, c)]
                best = None; bestv = None
                for e in cand:
                    v = self.P0.rank_of(add(c, e))
                    key2 = (v is None, v if v is not None else 0)
                    if best is None or key2 < bestv: best, bestv = e, key2
                out = {add(c, best)} if best is not None else set()
        else:
            out = set(ax_in)
        self.cache[key] = out
        return out

def run(k):
    S = Signed(k); d = S.d
    res = Counter(); ex = {}
    def fail(n, info): res[n] += 1; ex.setdefault(n, info)
    for c in S.native:
        lap = S.P0.lap(c)
        res['centres'] += 1
        if lap not in (-1, 0): fail('lap-other', (c, lap))
        for eta in (1, -1):
            Rc = S.R(eta, c)
            if lap == -1 and Rc != set(add(c, e) for e in ([(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)])): fail('quota-black%+d' % eta, c)
            if lap == 0 and len(Rc) != 1: fail('quota-white%+d' % eta, (c, Rc))
            if lap == 0 and S.P0.free(c):
                t = add(c, S.free_table(eta, c))
                if t not in [add(c, e) for e in ([(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)])]: fail('free-table-parity%+d' % eta, c)
            for i in Rc:
                if not S.price(i) <= S.price(c): fail('price%+d' % eta, (c, i))
                if not S.slip(eta, i) <= S.slip(eta, c): fail('Dslip%+d' % eta, (c, i))
                if not S.phi(eta, i) <= S.phi(eta, c): fail('Phi%+d' % eta, (c, i))
    return S, res, ex

def rank_test(S, eta):
    """R = Phi_eta + r, r periodic on the deck: difference constraints on the D classes (negative-cycle test)."""
    d = S.d; D = d * d + 2 * d - 1
    U = (d, 1); V = (1 - d, 1 + d)
    # Phi increments along the deck must be (-1, 2 eta) at every site sampled
    inc_ok = True
    for c in S.native:
        if S.phi(eta, add(c, U)) - S.phi(eta, c) != -1 or S.phi(eta, add(c, V)) - S.phi(eta, c) != 2 * eta: inc_ok = False; break
    cls = lambda z: (d * z[1] - z[0]) % D
    edges = []
    for x in S.native:
        for i in S.R(eta, x):
            w = -1 - (S.phi(eta, i) - S.phi(eta, x))
            edges.append((cls(x), cls(i), w))
    dist = {c: Fr(0) for c in range(D)}
    neg = False
    for it in range(D + 1):
        changed = False
        for (u, v, w) in edges:
            if dist[u] + w < dist[v]:
                dist[v] = dist[u] + w; changed = True
        if not changed: break
        if it == D: neg = True
    return inc_ok, (not neg)

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or list(range(0, 7))
    for k in ks:
        S, res, ex = run(k)
        print('k=%d d=%d' % (k, S.d), dict(res), {a: b for a, b in list(ex.items())[:2]}, flush=True)
        for eta in (1, -1):
            inc, feas = rank_test(S, eta)
            print('   rank R_%+d = Phi_%+d + r: Phi increments (-1,%+d) %s; periodic r with decrease along e_%+d edges: %s' % (eta, eta, 2 * eta, inc, eta, 'FEASIBLE' if feas else 'INFEASIBLE'), flush=True)
