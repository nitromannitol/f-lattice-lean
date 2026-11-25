"""The W1 policy at 3^k as defined from the note: retained := the Q_minus Retained edges
(w1_bulk_gate.py) with the selection at a white centre (laplacian 0): the prescribed input at a free centre, otherwise the
retained input of lower rank (rank of the target, the last representative offer of w1_free_root_gate.ranks). Black centres
(laplacian -1) retain both inputs. Field of the frame at 3^k: odd parent 0/1, even parent 1/(2k+1), child 1/(2k+3), eps = -1,
parentShift = (1,-1), shortShift = (-2,0), parentSlope z = -z2, price z = G z - G(z-(1,-1)) - z2, slip(eta,z) = G z - G(z + eta*shortShift),
chain(eta,z) = slip(eta,z) + price(z + eta*shortShift), reflectionI = (1,-1), eta = eps = -1 (and +1 where quantified).
Tests (seed = unseeded, the forced edges are the least fixed point of unit propagation over the unit squares):
  quota, priceNonincreasing, rawSlipNonincreasing (eta = +-1), chainNonincreasing (eta = +-1), reflection, forcedRetained,
  forcedWhiteUnique, privateSquare. westAtException is vacuous (eps = -1). Rank increments: see w1_rank_3k.py."""
import sys
from collections import Counter, deque
sys.path.insert(0, 'scripts')
import importlib.util
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
W = load('w', 'scripts/w1_field_3k.py')
B = load('b', 'scripts/w1_bulk_gate.py')
R0 = load('r', 'scripts/w1_free_root_gate.py')

def even(x): return (x[0] + x[1]) % 2 == 0
def inc_neg(x): return (x[0] - 1, x[1]) if even(x) else (x[0], x[1] - 1)
def inc_pos(x): return (x[0] + 1, x[1]) if even(x) else (x[0], x[1] + 1)
def axis(x): return [(-1, 0), (1, 0)] if even(x) else [(0, -1), (0, 1)]
def add(p, e): return (p[0] + e[0], p[1] + e[1])
I = (1, -1)

def prescribed(d, c):
    if even(c): return (-1, 0)
    if c[1] == 0 and 1 <= c[0] <= d: return (0, 1) if c[0] == d else (0, -1)
    return (0, 1)

class Policy:
    def __init__(self, k):
        self.f = W.Field(k); self.d = self.f.d
        self.edges = B.make(self.d)
        self.Fc = {}
        self.Rc = {}
        self.ranktab = {}
    def G(self, z):
        if z not in self.Fc: self.Fc[z] = self.f.F(z)
        return self.Fc[z]
    def lap(self, c):
        g = self.G(c)
        return (self.G(inc_neg(c)) - g) + (self.G(inc_pos(c)) - g)
    def free(self, c):
        return R0.native(self.d, c[0], c[1]) and R0.f.isfree(self.d, c[0], c[1])
    def rank_of(self, t):
        if t not in self.ranktab:
            rk = R0.ranks(self.d, t[0], t[1])
            vals = set(r for _, _, r in rk)
            self.ranktab[t] = (rk[-1][2] if rk else None, len(vals))
        return self.ranktab[t][0]
    def retained_minus(self, c):
        dirs, _ = self.edges(c[0], c[1])
        return [e for e in axis(c) if e in dirs]
    def R(self, c):
        """the policy's retained inputs at centre c"""
        if c in self.Rc: return self.Rc[c]
        l = self.lap(c)
        if l == -1:
            out = {inc_neg(c), inc_pos(c)}
        else:
            cand = self.retained_minus(c)
            if l == 0:
                if self.free(c) and prescribed(self.d, c) in cand:
                    out = {add(c, prescribed(self.d, c))}
                elif cand:
                    best = None; bestv = None
                    for e in cand:
                        v = self.rank_of(add(c, e))
                        key = (v is None, v if v is not None else 0)
                        if best is None or key < bestv: best, bestv = e, key
                    out = {add(c, best)}
                else:
                    out = set()
            else:
                out = {add(c, e) for e in cand}
        self.Rc[c] = out
        return out
    def forced_set(self, box):
        """least fixed point of unit propagation over unit squares with corners in box (unseeded ForcedEdge)."""
        Fs = set()
        changed = True
        squares = [(a, b) for a in range(box[0], box[1]) for b in range(box[2], box[3])]
        while changed:
            changed = False
            for (a, b) in squares:
                S = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                for c in S:
                    if self.lap(c) != 0: continue
                    for o in (inc_neg(c), inc_pos(c)):
                        if o in S or (c, o) in Fs: continue
                        ok = True
                        for c2 in S:
                            if c2 == c: continue
                            l2 = self.lap(c2)
                            if l2 == -1: continue
                            if l2 == 0 and any((c2, s) in Fs for s in (inc_neg(c2), inc_pos(c2)) if s in S): continue
                            ok = False; break
                        if ok:
                            Fs.add((c, o)); changed = True
        return Fs

def check(k, margin=2):
    P = Policy(k); d = P.d
    native = [c for c in P.f.raw]
    xs = [c[0] for c in native]; ys = [c[1] for c in native]
    box = (min(xs) - margin, max(xs) + margin + 1, min(ys) - margin, max(ys) + margin + 1)
    Fs = P.forced_set(box)
    res = Counter(); ex = {}
    def fail(name, info):
        res[name] += 1
        ex.setdefault(name, info)
    for c in native:
        l = P.lap(c)
        res['centres'] += 1
        Rc = P.R(c)
        # quota
        if l == -1 and Rc != {inc_neg(c), inc_pos(c)}: fail('quota-black', c)
        if l == 0 and len(Rc) != 1: fail('quota-white', (c, Rc))
        if l not in (-1, 0): fail('lap-other', (c, l))
        for i in Rc:
            if not (i in [inc_neg(c), inc_pos(c)]): fail('edge-not-input', (c, i))
            # price
            price = lambda z: P.G(z) - P.G((z[0] - 1, z[1] + 1)) - z[1]
            if not price(i) <= price(c): fail('price', (c, i))
            for eta in (-1, 1):
                slip = lambda z: P.G(z) - P.G((z[0] - 2 * eta, z[1]))
                if not slip(i) <= slip(c): fail('rawslip%+d' % eta, (c, i))
                chain = lambda z: slip(z) + price((z[0] - 2 * eta, z[1]))
                if not chain(i) <= chain(c): fail('chain%+d' % eta, (c, i))
            # reflection
            if l == -1 or (c, i) in Fs:
                if i not in [inc_neg(c), inc_pos(c)] and False: pass
                rc = (I[0] - c[0], I[1] - c[1]); ri = (I[0] - i[0], I[1] - i[1])
                if ri not in P.R(rc): fail('reflection', (c, i))
        # forced
        for o in (inc_neg(c), inc_pos(c)):
            if (c, o) in Fs:
                if o not in Rc: fail('forcedRetained', (c, o))
                if l == 0 and Rc != {o}: fail('forcedWhiteUnique', (c, o, Rc))
    return d, res, ex

if __name__ == '__main__':
    for k in range(0, 7):
        d, res, ex = check(k)
        print('k=%d d=%d' % (k, d), dict(res), {a: b for a, b in list(ex.items())[:2]}, flush=True)

def private_squares(k, margin=2):
    """privateSquare: a forced non-seed white c lies in a unit square whose other corners reach c by retained-input chains."""
    P = Policy(k); d = P.d
    native = list(P.f.raw)
    xs = [c[0] for c in native]; ys = [c[1] for c in native]
    box = (min(xs) - margin, max(xs) + margin + 1, min(ys) - margin, max(ys) + margin + 1)
    Fs = P.forced_set(box)
    lo = (min(xs) - 3 * margin, max(xs) + 3 * margin, min(ys) - 3 * margin, max(ys) + 3 * margin)
    def reach(src, dst):
        seen = {src}; dq = deque([src])
        while dq:
            x = dq.popleft()
            if x == dst: return True
            for y in P.R(x):
                if y not in seen and lo[0] <= y[0] <= lo[1] and lo[2] <= y[1] <= lo[3]:
                    seen.add(y); dq.append(y)
        return False
    fails = []; checked = 0
    for (c, o) in Fs:
        if P.lap(c) != 0: continue
        checked += 1
        ok = False
        for a in (c[0] - 1, c[0]):
            for b in (c[1] - 1, c[1]):
                S = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if c not in S: continue
                if all(reach(c2, c) for c2 in S if c2 != c):
                    ok = True; break
            if ok: break
        if not ok: fails.append((c, o))
    return d, checked, fails

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'private':
    for k in range(0, 7):
        d, checked, fails = private_squares(k)
        print('privateSquare k=%d d=%d forced whites %d violations %d' % (k, d, checked, len(fails)), fails[:3], flush=True)
