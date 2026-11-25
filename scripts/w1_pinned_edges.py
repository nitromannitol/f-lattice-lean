"""Pinned V0 / V_{+-1} retained edges of the note (H_SOURCE_ANCESTRAL_CLOSURE §1) against the canonical S3 policy
(rules of w3's scripts/s3_policy_check.py), on the CONJUGATE field standard(cw), cw = conjWord(u), u in words(4).

Pins (child coordinates of the conjugate frame; vFirst=(0,0), hFirst=(1,0)):
  both signs:  centre (0,0) keeps east input (1,0)
  eta=+1:      centre (0,1) keeps south input (0,0)
  eta=-1:      centre (1,-1) keeps west input (0,-1); centre (0,-1) keeps north input (0,0)
Admissibility as in s3_policy_check: a black centre keeps both inputs (permitted and P,J weakly lower); a white centre keeps
one permitted input with P,J weakly lower, strict preferred. The short shift is (2 eta D, 2 eta N) with eta the sign under test."""
import sys
sys.path.insert(0, 'scripts')
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import cut_on, words

PINS = {
    'V0 east (both signs)': ((0, 0), (1, 0), None),
    'eta+ V1 south': ((0, 1), (0, 0), +1),
    'eta- V_-1 west': ((1, -1), (0, -1), -1),
    'eta- (0,-1) north': ((0, -1), (0, 0), -1),
}

def conj_of(u):
    return tuple(pl.swap(pl.odd_birth_prefix(list(u))))

def check(cw, eta):
    w = list(cw)
    F, _ = pl.standard(tuple(w))
    fr = oc.frame(w)
    N, D, n, d, T = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"]
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, 1)
    short = (2 * eta * D, 2 * eta * N)
    def D1(z):
        return F(z) - F((z[0] + short[0], z[1] + short[1]))
    def perm(c, i):
        return D1(i) - D1(c) <= 0
    def admissible(c, i):
        dP = P(i) - P(c); dJ = J(i) - J(c)
        return perm(c, i) and dP <= 0 and dJ <= 0, (dP < 0 or dJ < 0)
    out = {}
    for name, (c, i, e) in PINS.items():
        if e is not None and e != eta:
            continue
        lap = pl.lap(F, c)
        ok, strict = admissible(c, i)
        # the other input, for a white centre (is the pinned input the unique witness?)
        others = [j for j in (oc.incoming_neg(c), oc.incoming_pos(c)) if j != i]
        other_ok = [admissible(c, j)[0] for j in others]
        out[name] = dict(in_poly=oc.in_polygon(c, fr), lap=lap, admissible=ok, strict=strict, other_admissible=other_ok)
    return out

def job(u):
    cw = conj_of(u)
    res = {}
    for eta in (+1, -1):
        try:
            res[eta] = check(cw, eta)
        except Exception as ex:
            res[eta] = repr(ex)
    return u, cw, res

if __name__ == '__main__':
    ws = list(words(4))
    tot = defaultdict(int)
    fails = []
    with Pool(8) as pool:
        for u, cw, res in pool.imap_unordered(job, ws):
            for eta, r in res.items():
                if isinstance(r, str):
                    tot['error'] += 1
                    fails.append((u, cw, eta, r))
                    continue
                for name, info in r.items():
                    key = (eta, name, 'admissible' if info['admissible'] else 'NOT admissible')
                    tot[key] += 1
                    if not info['admissible'] and len(fails) < 12:
                        fails.append((u, cw, eta, name, info))
    for k in sorted(tot, key=str):
        print(k, tot[k])
    print('example failures:')
    for f in fails[:8]:
        print(f)
