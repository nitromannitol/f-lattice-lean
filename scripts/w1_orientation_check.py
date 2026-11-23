"""Task 64 orientation check (lead directive): on the canonical S3 policy, which orientation do the forced whites' squares have?

The canonical policy is the construction of s3_policy_check (deck representatives, extended to all sites by the even deck shifts):
black centres keep both inputs; a white centre keeps one permitted input weakly lower in (P, J), strict drops preferred.
Two choice rules for the white witness are run, to test robustness: 'neg' (among strict witnesses, the input with the smaller (dP, dJ),
ties to incomingNeg) and 'pos' (ties to incomingPos).

Forcing model (as w1_forcing_check): a white c is forced by a unit square Q in E° with its rejected input p(c) (the input of c inside Q)
and its pointer o(c) (the other input, outside Q); every other corner x of Q is black, or white with its in-square input forced earlier.
Rounds give the least fixed point. For each forced white at its first round, with its square Q, the in-square chain
n1 = p(c), n2 = p(n1), n3 = p(n2) (p(n3) = c) is recorded with the kept-edge pattern
  Kc = policy keeps (c, n1)  [root keeps its rejected input]
  Ko = policy keeps (c, o)   [root keeps its pointer]
  K1 = policy keeps (n1, n2), K2 = policy keeps (n2, n3), K3 = policy keeps (n3, c).
Lead orientation: Kc False, K1 K2 K3 True (corners keep, last keeps the root). Our field: Kc True, K1 True, K2 True.
"""
import sys
from pathlib import Path
from collections import Counter, defaultdict
from multiprocessing import Pool
import importlib.util

sys.path.insert(0, str(Path(__file__).parent))
import permit_local as pl  # noqa: E402
import open_inputs_check as oc  # noqa: E402
from exact_quotient import cut_on, words  # noqa: E402

_sv = sys.argv
sys.argv = [_sv[0], '2', '30']
spec = importlib.util.spec_from_file_location('cc', str(Path(__file__).parent / 'w1_collar_check.py'))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)
sys.argv = _sv


def ins(z):
    return [oc.incoming_neg(z), oc.incoming_pos(z)]


class Policy:
    def __init__(self, w, rule):
        self.w = list(w)
        self.rule = rule
        F, _ = pl.standard(tuple(w))
        self.F = F
        fr = oc.frame(w)
        self.fr = fr
        N, D, n, d, T, eps = fr['N'], fr['D'], fr['n'], fr['d'], fr['T'], fr['eps']
        self.P = cut_on(F, w, 1, 0, 1)
        self.J = cut_on(F, w, 0, 1, 1)
        short = (2 * eps * D, 2 * eps * N)
        self.U = (d, n)
        self.V = (n - d, n + d)
        self.short = short
        self.tlo_even, self.tlo_odd = 2 - T, n - T
        self.slo_even, self.slo_odd = 0, 2 - d + n
        self.T = T
        self.n, self.d = n, d
        self.cache = {}
        self.violations = Counter()

    def perm(self, c, i):
        s = self.short
        def D1(z):
            return self.F(z) - self.F((z[0] + s[0], z[1] + s[1]))
        return D1(i) - D1(c) <= 0

    def tg(self, z):
        return self.n * z[0] - self.d * z[1]

    def sg(self, z):
        return (self.d + self.n) * z[0] + (self.d - self.n) * z[1]

    def reduce(self, z):
        even = oc.even_site(z)
        tlo = self.tlo_even if even else self.tlo_odd
        slo = self.slo_even if even else self.slo_odd
        T = self.T
        b = (self.tg(z) - tlo) // T
        z1 = (z[0] + b * self.V[0], z[1] + b * self.V[1])
        a = -((self.sg(z1) - slo) // T)
        z2 = (z1[0] + a * self.U[0], z1[1] + a * self.U[1])
        if not oc.in_polygon(z2, self.fr):
            raise ValueError('reduce left the polygon')
        return z2

    def offsets(self, r):
        """The kept inputs of the polygon site r, as offsets from r."""
        if r in self.cache:
            return self.cache[r]
        lv = pl.lap(self.F, r)
        info = []
        for i in ins(r):
            info.append((i, self.P(i) - self.P(r), self.J(i) - self.J(r), self.perm(r, i)))
        if lv == -1:
            keep = [i for (i, dP, dJ, pf) in info]
            for (i, dP, dJ, pf) in info:
                if not pf:
                    self.violations['black_not_permitted'] += 1
                if not (dP <= 0 and dJ <= 0):
                    self.violations['black_not_monotone'] += 1
        else:
            cand = [(i, dP, dJ) for (i, dP, dJ, pf) in info if pf and dP <= 0 and dJ <= 0]
            if not cand:
                self.violations['white_no_witness'] += 1
                keep = []
            else:
                strict = [c for c in cand if c[1] < 0 or c[2] < 0]
                if strict:
                    if self.rule == 'neg':
                        strict.sort(key=lambda c: (c[1] + c[2], c[1], 0 if c[0] == oc.incoming_neg(r) else 1))
                    else:
                        strict.sort(key=lambda c: (c[1] + c[2], c[1], 0 if c[0] == oc.incoming_pos(r) else 1))
                    keep = [strict[0][0]]
                else:
                    keep = [cand[0][0]] if self.rule == 'neg' else [cand[-1][0]]
        off = [(i[0] - r[0], i[1] - r[1]) for i in keep]
        self.cache[r] = off
        return off

    def keeps(self, z, j):
        z2 = self.reduce(z)
        off = (j[0] - z[0], j[1] - z[1])
        return off in self.offsets(z2)


def run(args):
    w, rule = args
    w = list(w)
    pol = Policy(w, rule)
    Pc = cc.params(tuple(w))
    M = 3 * Pc['d'] + 3
    E0 = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if cc.strict(Pc, (x, y))]
    Eset = set(E0)
    bad_in_polygon = sum(1 for z in E0 if not oc.in_polygon(z, pol.fr))
    lap = lambda z: pl.lap(pol.F, z)
    whites = [c for c in E0 if lap(c) == 0]
    squares = defaultdict(list)
    for c in whites:
        for a in (c[0] - 1, c[0]):
            for b in (c[1] - 1, c[1]):
                corners = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
                if all(q in Eset for q in corners):
                    squares[c].append(corners)
    forced = {}      # (c, pointer) -> round
    record = []      # (c, square, pointer o) at the first round
    rnd = 0
    while True:
        new = []
        for c in whites:
            if any(k[0] == c for k in forced):
                continue
            for Q in squares[c]:
                Qs = set(Q)
                if not all(x == c or lap(x) == -1 or lap(x) == 0 for x in Q):
                    continue
                ok = True
                for x in Q:
                    if x == c or lap(x) == -1:
                        continue
                    px = [y for y in ins(x) if y in Qs]
                    if len(px) != 1 or (x, px[0]) not in forced:
                        ok = False
                        break
                if not ok:
                    continue
                pin = [y for y in ins(c) if y in Qs]
                if len(pin) != 1:
                    continue
                out = [y for y in ins(c) if y not in Qs]
                if len(out) != 1:
                    continue
                new.append((c, tuple(Q), out[0]))
        if not new:
            break
        rnd += 1
        for (c, Q, o) in new:
            forced.setdefault((c, o), rnd)
            record.append((c, Q, o, rnd))
    unforced = [c for c in whites if not any(k[0] == c for k in forced)]
    pats = Counter()
    per_white = defaultdict(set)
    for (c, Q, o, r) in record:
        Qs = set(Q)
        n1 = [y for y in ins(c) if y in Qs][0]
        n2 = [y for y in ins(n1) if y in Qs][0]
        n3 = [y for y in ins(n2) if y in Qs][0]
        assert [y for y in ins(n3) if y in Qs] == [c] or c in ins(n3), (c, Q)
        Kc = pol.keeps(c, n1)
        Ko = pol.keeps(c, o)
        K1 = pol.keeps(n1, n2)
        K2 = pol.keeps(n2, n3)
        K3 = pol.keeps(n3, c)
        pats[(Kc, Ko, K1, K2, K3)] += 1
        per_white[c].add((Kc, Ko, K1, K2, K3))
    # per white: lead pattern (root rejects, corners keep, last keeps root), our pattern (root keeps rejected, corners keep first two),
    # full kept cycle (all four in-square edges kept)
    cls = Counter()
    for c, ps in per_white.items():
        lead = any((not a) and b1 and b2 and b3 for (a, _, b1, b2, b3) in ps)
        ours = any(a and b1 and b2 for (a, _, b1, b2, _) in ps)
        cyc = any(a and b1 and b2 and b3 for (a, _, b1, b2, b3) in ps)
        cls['white_forced'] += 1
        cls['has_lead'] += int(lead)
        cls['has_ours'] += int(ours)
        cls['has_full_cycle'] += int(cyc)
        cls['lead_and_no_fullcycle_squares_only'] += int(lead and not any(a and b1 and b2 and b3 for (a, _, b1, b2, b3) in ps))
        cls['no_lead_square'] += int(not lead)
    return w, dict(pats), len(whites), len(unforced), bad_in_polygon, dict(pol.violations), dict(cls)


if __name__ == '__main__':
    rule = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] in ('neg', 'pos') else 'neg'
    ws = list(words(4))
    tot = Counter()
    unf = 0
    whites_total = 0
    bad_poly = 0
    viol = Counter()
    cls_tot = Counter()
    with Pool(8) as pool:
        for w, pats, nw, nu, bp, v, cls in pool.imap_unordered(run, [(w, rule) for w in ws]):
            tot.update(pats)
            unf += nu
            whites_total += nw
            bad_poly += bp
            viol.update(v)
            cls_tot.update(cls)
    print('RULE', rule, 'WORDS', len(ws), 'WHITES', whites_total, 'UNFORCED', unf, 'E0_NOT_IN_POLYGON', bad_poly)
    print('POLICY_VIOLATIONS', dict(viol))
    print('PATTERNS (Kc, Ko, K1, K2, K3): count', dict(tot))
    print('PER WHITE', dict(cls_tot))
