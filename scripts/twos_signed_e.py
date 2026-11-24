"""Signed canonical policies e(-1,eta) of the twos words 2^K (K = 1..4), ported from the archive pure2_initialization
(physical_unit_probe.run(K) forced inputs, check_flat_rank_formula.py / discover_flat_rank.py H/V classes) onto
pl.standard(2^K) and the Lean conventions of Potentials.lean at frameAt (replicate K two), eps = -1:
  price z = F z - F (z - parentShift) + parentSlope z, parentShift = (1, -n), parentSlope z = K z1 - (K+1) z2,
  slip eta z = F z - F (z + eta shortShift), shortShift = (-2(K+1), -2K),
  roundedSlip eta z = (slip eta z + 1) / 2   (the field J),   chainPotential eta z = slip eta z + price (z + eta shortShift).
Word exponent K = k+1 of frameAt (replicate (k+1) two); n = 2K+1, d = 2K+3, a = 2K+2, U = (d,n), V = (-2,2a),
T = 2a^2 + 4a - 2 = d^2 + 2dn - n^2, key z = (n z0 - d z1) mod T (Lambda-invariant, gcd(n,T) = 1).

Selection (the archive policy): black (laplacian -1) keeps both inputs; white (laplacian 0) keeps one input c + dirs_eta(key c),
where dirs_eta = forced (unit propagation of the square clauses, physical_unit_probe.run) overridden on the free classes:
  H = (1,0), (i, i-2) for 2 <= i <= a, (a+1, a-2): H_0 = (1,0) keeps (0,-eta); other H keep east if the sum is even, north if odd;
  V = (0,i) for 0 <= i < a, (-1,i) for a <= i < 2a: V_0 = (0,0) keeps east; other V keep (eta,0) if the sum is even, (0,-eta) if odd.

Checks, on one representative per key class (edge differences of P, J, D, Phi are Lambda-invariant):
  field: F(z+U) = F(z), F(z+V) = F(z) + t(z) + cV with t = n z0 - d z1, cV = 1 - a^2 - 3a; laplacian in {-1, 0};
  quota: black keeps both inputs; white keeps exactly one, a unit input of its parity;
  monotone along selected edges: P (price), J (roundedSlip eta), D (slip eta), Phi (chainPotential eta);
  square clauses: every unit square has a white corner whose selected input lies outside the square;
  free classes: H/V sites that are white get the explicit prescription; black free sites are counted.
Not checked here: permitted (slipPermits), westAtException (eps = -1, vacuous), the strict rank (rawall.py / globalrank.py).
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import permit_local as pl  # noqa: E402


def ip(z):
    x, y = z
    return ((x - 1, y), (x + 1, y)) if (x + y) % 2 == 0 else ((x, y - 1), (x, y + 1))


def add(p, e):
    return (p[0] + e[0], p[1] + e[1])


def neg(e):
    return (-e[0], -e[1])


class Twos:
    def __init__(self, K):
        self.K = K
        self.a = 2 * K + 2
        self.n = 2 * K + 1
        self.d = 2 * K + 3
        self.T = 2 * self.a * self.a + 4 * self.a - 2
        assert self.T == self.d * self.d + 2 * self.d * self.n - self.n * self.n
        self.F0 = pl.standard((2,) * K)[0]
        self.Fc = {}
        self.parentShift = (1, -self.n)
        self.shortShift = (-2 * (K + 1), -2 * K)

    # field and the Lean prices
    def F(self, z):
        if z not in self.Fc:
            self.Fc[z] = self.F0(z)
        return self.Fc[z]

    def key(self, z):
        return (self.n * z[0] - self.d * z[1]) % self.T

    def lap(self, c):
        return self.F(ip(c)[0]) + self.F(ip(c)[1]) - 2 * self.F(c)

    def parentSlope(self, z):
        return self.K * z[0] - (self.K + 1) * z[1]

    def price(self, z):
        return self.F(z) - self.F(add(z, neg(self.parentShift))) + self.parentSlope(z)

    def slip(self, eta, z):
        return self.F(z) - self.F(add(z, (eta * self.shortShift[0], eta * self.shortShift[1])))

    def rounded(self, eta, z):
        return (self.slip(eta, z) + 1) // 2

    def chain(self, eta, z):
        return self.slip(eta, z) + self.price(add(z, (eta * self.shortShift[0], eta * self.shortShift[1])))

    def rep(self, r):
        # n * x = r (mod T) has a solution x in [0, T) since gcd(n, T) = 1
        x = (r * self.ninv) % self.T
        return (x, 0)

    @property
    def ninv(self):
        if not hasattr(self, '_ninv'):
            # extended Euclid on (n, T): find s with n * s = 1 (mod T)
            r0, r1, s0, s1 = self.n, self.T, 1, 0
            while r1:
                q = r0 // r1
                r0, r1 = r1, r0 - q * r1
                s0, s1 = s1, s0 - q * s1
            assert r0 == 1, 'gcd(n, T) != 1'
            self._ninv = s0 % self.T
        return self._ninv

    # the archive's forced inputs: square clauses keyed by residues, unit propagation
    def clauses(self):
        out = []
        for r in range(self.T):
            x, y = self.rep(r)
            S = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
            cc = []
            for v in S:
                if self.lap(v) == 0:
                    q = next(u for u in ip(v) if u not in S)
                    cc.append((self.key(v), add(q, neg(v))))
            assert cc, (r, (x, y))
            out.append(cc)
        return out

    def forced(self, cl):
        forced = {}
        rounds = 0
        while True:
            new = {}
            for cc in cl:
                if any(forced.get(k) == v for k, v in cc):
                    continue
                left = [(k, v) for k, v in cc if k not in forced]
                assert left
                if len(left) == 1:
                    k, v = left[0]
                    assert k not in new or new[k] == v, ('conflict', k)
                    new[k] = v
            if not new:
                break
            rounds += 1
            forced.update(new)
        return forced, rounds

    def H(self):
        a = self.a
        return [(1, 0)] + [(i, i - 2) for i in range(2, a + 1)] + [(a + 1, a - 2)]

    def V(self):
        a = self.a
        return [(0, i) for i in range(a)] + [(-1, i) for i in range(a, 2 * a)]

    def dirs(self, eta, forced):
        out = dict(forced)
        for j, v in enumerate(self.H()):
            out[self.key(v)] = (0, -eta) if j == 0 else ((1, 0) if sum(v) % 2 == 0 else (0, 1))
        for j, v in enumerate(self.V()):
            out[self.key(v)] = (1, 0) if j == 0 else ((eta, 0) if sum(v) % 2 == 0 else (0, -eta))
        return out

    def retained(self, dirs, c):
        l = self.lap(c)
        if l == -1:
            return set(ip(c))
        k = self.key(c)
        if k not in dirs:
            return None
        return {add(c, dirs[k])}

    def field_check(self):
        bad = Counter()
        a, n, d = self.a, self.n, self.d
        U = (d, n)
        V = (-2, 2 * a)
        cV = 1 - a * a - 3 * a
        for x in range(-3, 4):
            for y in range(-3, 4):
                z = (x, y)
                if self.F(add(z, U)) != self.F(z):
                    bad['U'] += 1
                if self.F(add(z, V)) != self.F(z) + n * x - d * y + cV:
                    bad['V'] += 1
                if self.lap(z) not in (-1, 0):
                    bad['lap'] += 1
        return bad


def run(K):
    t = Twos(K)
    res = Counter()
    res.update({('field', k): v for k, v in t.field_check().items()})
    cl = t.clauses()
    forced, rounds = t.forced(cl)
    res['rounds'] = rounds
    res['forced'] = len(forced)
    hk = [t.key(v) for v in t.H()] + [t.key(v) for v in t.V()]
    assert len(set(hk)) == len(hk), 'free classes collide'
    res['freeWhite'] = sum(1 for v in t.H() + t.V() if t.lap(v) == 0)
    res['freeBlack'] = sum(1 for v in t.H() + t.V() if t.lap(v) == -1)
    res['whites'] = sum(1 for r in range(t.T) if t.lap(t.rep(r)) == 0)
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)
        for r in range(t.T):
            c = t.rep(r)
            l = t.lap(c)
            if l not in (-1, 0):
                res[('bad-lap', eta)] += 1
                continue
            R = t.retained(dirs, c)
            if R is None:
                res[('nodir', eta)] += 1
                continue
            if l == 0:
                (i,) = tuple(R)
                if i not in ip(c):
                    res[('edge', eta)] += 1
            for i in R:
                res[('edges', eta)] += 1
                if not t.price(i) <= t.price(c):
                    res[('P', eta)] += 1
                if not t.rounded(eta, i) <= t.rounded(eta, c):
                    res[('J', eta)] += 1
                if not t.slip(eta, i) <= t.slip(eta, c):
                    res[('D', eta)] += 1
                if not t.chain(eta, i) <= t.chain(eta, c):
                    res[('Phi', eta)] += 1
        # square clauses on the final policy, at one representative per residue
        for r in range(t.T):
            x, y = t.rep(r)
            S = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
            ok = False
            for v in S:
                if t.lap(v) != 0:
                    continue
                R = t.retained(dirs, v)
                if R and any(q not in S for q in R):
                    ok = True
            if not ok:
                res[('square', eta)] += 1
        # free classes: the explicit prescription at white free sites
        for j, v in enumerate(t.H() + t.V()):
            if t.lap(v) == 0:
                if t.retained(dirs, v) is None:
                    res[('prescribed', eta)] += 1
    return t, res


def strict_rank(K):
    """The Lean strictRank field: rank i < rank c for every selected input i of c with P(i) = P(c) and J_eta(i) = J_eta(c).
    P and J change by constants under the period lattice, so the condition is on residue classes: the directed graph on the
    T classes (edges key c -> key i for such selected pairs) must have no cycle; a witness rank is the longest path to a sink."""
    t = Twos(K)
    cl = t.clauses()
    forced, _ = t.forced(cl)
    out = {}
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)
        succ = {r: set() for r in range(t.T)}
        edges = 0
        for r in range(t.T):
            c = t.rep(r)
            for i in t.retained(dirs, c):
                if t.price(i) == t.price(c) and t.rounded(eta, i) == t.rounded(eta, c):
                    edges += 1
                    succ[r].add(t.key(i))
        rank, onstack = {}, set()

        def visit(r):
            if r in rank:
                return rank[r]
            if r in onstack:
                raise ValueError('cycle through class %d' % r)
            onstack.add(r)
            v = 0
            for s in succ[r]:
                v = max(v, visit(s) + 1)
            onstack.discard(r)
            rank[r] = v
            return v
        try:
            for r in range(t.T):
                visit(r)
            ok = all(rank[s] < rank[r] for r in succ for s in succ[r])
            out[eta] = ('acyclic', edges, max(rank.values()), ok)
        except ValueError as e:
            out[eta] = ('CYCLE', edges, str(e), False)
    return out


def rank_table(Ks):
    sys.setrecursionlimit(20000)
    for K in Ks:
        r = strict_rank(K)
        for eta in (1, -1):
            print('K=%d eta=%+d  (P,J)-flat selected edges %3d  %s  max rank %s  witness ok %s'
                  % (K, eta, r[eta][1], r[eta][0], r[eta][2], r[eta][3]), flush=True)


def table(Ks):
    head = ('K  a   T  whites forced freeW freeB  fieldFail  eta  edges    P    J    D  Phi  square  nodir  edge  prescr  status')
    print(head)
    allok = True
    for K in Ks:
        t, res = run(K)
        fld = res[('field', 'U')] + res[('field', 'V')] + res[('field', 'lap')]
        for eta in (1, -1):
            cnt = {nm: res[(nm, eta)] for nm in ('edges', 'P', 'J', 'D', 'Phi', 'square', 'nodir', 'edge', 'prescribed')}
            bad = sum(cnt[nm] for nm in ('P', 'J', 'D', 'Phi', 'square', 'nodir', 'edge', 'prescribed')) \
                + res[('bad-lap', eta)] + fld
            allok = allok and bad == 0
            print('%d %3d %3d %6d %6d %5d %5d %9d  %+d  %5d %4d %4d %4d %4d %7d %6d %5d %7d  %s' % (
                K, t.a, t.T, res['whites'], res['forced'], res['freeWhite'], res['freeBlack'], fld, eta,
                cnt['edges'], cnt['P'], cnt['J'], cnt['D'], cnt['Phi'], cnt['square'], cnt['nodir'], cnt['edge'],
                cnt['prescribed'], 'ok' if bad == 0 else 'FAIL'), flush=True)
    print('ALL OK' if allok else 'FAILURES PRESENT')


def mutation(K):
    """Control: every selected input replaced by its opposite. The P, J, D, Phi and square checks must fail."""
    orig = Twos.dirs
    Twos.dirs = lambda self, eta, forced: {k: (-v[0], -v[1]) for k, v in orig(self, eta, forced).items()}
    try:
        _, res = run(K)
    finally:
        Twos.dirs = orig
    print('control K=%d (selected inputs flipped):' % K, ', '.join(
        '%s %d/%d' % (nm, res[(nm, 1)], res[(nm, -1)]) for nm in ('P', 'J', 'D', 'Phi', 'square')),
        '(eta=+1/-1 failure counts)')
    return all(res[(nm, eta)] > 0 for nm in ('P', 'J', 'D', 'Phi', 'square') for eta in (1, -1))


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'table'
    Ks = [int(a) for a in sys.argv[2:]] or [1, 2, 3, 4]
    if mode == 'table':
        table(Ks)
    elif mode == 'mutation':
        print('control detects every check:', all(mutation(K) for K in Ks))
    elif mode == 'rank':
        rank_table(Ks)
    else:
        raise SystemExit('usage: twos_signed_e.py [table|mutation|rank] K...')
