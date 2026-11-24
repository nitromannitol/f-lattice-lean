"""Signed policies e(-1,eta) with forced arrows seeded by the note's free table (task 118, W1 base). The note's forced arrows come
from unit propagation (ForcedEdge with seed) whose seeds are the free-table selections. White selection: the seeded forced arrow if
forced; otherwise even: west for x<=0, east for x>=2; odd: lower-rank retained input (plus rule for eta=+1, minus for eta=-1).
Black: both inputs; free centres: the table. Tests as in w1_signed_3k.py: quota, P, D_eta, Phi_eta nonincreasing, and the periodic
rank R_eta = Phi_eta + r."""
import sys
from collections import Counter
sys.path.insert(0, 'scripts')
import importlib.util
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
SG = load('sg', 'scripts/w1_signed_3k.py')
add = SG.add; even = SG.even

class Seeded(SG.Signed):
    def __init__(self, k):
        super().__init__(k)
        self.forced = {}
        xs = [c[0] for c in self.native]; ys = [c[1] for c in self.native]
        self.box = (min(xs) - 2, max(xs) + 3, min(ys) - 2, max(ys) + 3)
    def forced_for(self, eta):
        if eta in self.forced: return self.forced[eta]
        P0 = self.P0
        seeds = set()
        for c in self.native:
            if P0.free(c):
                seeds.add((c, add(c, self.free_table(eta, c))))
        Fs = set(seeds)
        changed = True
        a0, a1, b0, b1 = self.box
        squares = [(a, b) for a in range(a0, a1) for b in range(b0, b1)]
        while changed:
            changed = False
            for (a, b) in squares:
                S = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                for c in S:
                    if P0.lap(c) != 0: continue
                    for o in (SG.PL.inc_neg(c) if hasattr(SG.PL, 'inc_neg') else (c[0] - 1, c[1]) if even(c) else (c[0], c[1] - 1),
                              (c[0] + 1, c[1]) if even(c) else (c[0], c[1] + 1)):
                        if o in S or (c, o) in Fs: continue
                        ok = True
                        for c2 in S:
                            if c2 == c: continue
                            l2 = P0.lap(c2)
                            if l2 == -1: continue
                            if l2 == 0 and any((c2, s) in Fs for s in ((c2[0] - 1, c2[1]) if even(c2) else (c2[0], c2[1] - 1),
                                                                    (c2[0] + 1, c2[1]) if even(c2) else (c2[0], c2[1] + 1)) if s in S):
                                continue
                            ok = False; break
                        if ok:
                            Fs.add((c, o)); changed = True
        self.forced[eta] = Fs
        return Fs
    def R(self, eta, c):
        key = (eta, c)
        if key in self.cache: return self.cache[key]
        lap = self.P0.lap(c)
        axin = [add(c, e) for e in ([(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)])]
        if lap == -1:
            out = set(axin)
        elif lap == 0:
            if self.P0.free(c):
                out = {add(c, self.free_table(eta, c))}
            else:
                fo = [o for (cc, o) in self.forced_for(eta) if cc == c]
                if fo:
                    out = {fo[0]}
                elif even(c):
                    out = {add(c, (-1, 0))} if c[0] <= 0 else {add(c, (1, 0))}
                else:
                    cand = self.candidates(eta, c)
                    best = None; bestv = None
                    for e in cand:
                        v = self.P0.rank_of(add(c, e))
                        key2 = (v is None, v if v is not None else 0)
                        if best is None or key2 < bestv: best, bestv = e, key2
                    out = {add(c, best)} if best is not None else set()
        else:
            out = set(axin)
        self.cache[key] = out
        return out

if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or list(range(0, 7))
    for k in ks:
        SG.Signed.__init__  # noqa
        S = Seeded(k)
        # reuse the test driver of w1_signed_3k with this policy
        SG.run.__globals__['Signed'] = Seeded
        d, res, ex = None, None, None
        from collections import Counter as C
        res = C(); ex = {}
        def fail(n, info): res[n] += 1; ex.setdefault(n, info)
        for c in S.native:
            lap = S.P0.lap(c); res['centres'] += 1
            for eta in (1, -1):
                Rc = S.R(eta, c)
                if lap == -1 and Rc != set(add(c, e) for e in ([(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)])): fail('quota-black%+d' % eta, c)
                if lap == 0 and len(Rc) != 1: fail('quota-white%+d' % eta, (c, Rc))
                for i in Rc:
                    if not S.price(i) <= S.price(c): fail('price%+d' % eta, (c, i))
                    if not S.slip(eta, i) <= S.slip(eta, c): fail('Dslip%+d' % eta, (c, i))
                    if not S.phi(eta, i) <= S.phi(eta, c): fail('Phi%+d' % eta, (c, i))
        print('seeded k=%d d=%d' % (k, S.d), dict(res), {a: b for a, b in list(ex.items())[:2]}, flush=True)
        for eta in (1, -1):
            inc, feas = SG.rank_test(S, eta)
            print('   rank R_%+d = Phi_%+d + r: increments %s; periodic r decreasing on e_%+d: %s' % (eta, eta, inc, eta, 'FEASIBLE' if feas else 'INFEASIBLE'), flush=True)
