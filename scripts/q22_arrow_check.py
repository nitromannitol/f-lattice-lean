"""Q22 finite check: the admissible arrows of the earlier signed policy on the 116 proper words of length <= 4.

Pin reading (the one reproducing the fix's count, 290 of 290): the north pin (0,-1) -> (0,0) at H_last - U' applies to eta = -1 only,
as in scripts/w1_pinned_edges.py. Read with the north pin also for eta = +1, the count is 348 of 348, and every arrow is admissible in
both readings. Admissible here means only the per-arrow monotonicity of the primitive price, the signed raw slip and the rounded slip; the
quota and square clauses are not checked. Run: python3 scripts/q22_arrow_check.py (north_both=True gives the 348 reading).

Field model imported read-only from the repo's scripts/permit_local.py.
Conventions (from Lean ChildFrame / Potentials and Q22.md):
  receiver sign eta = Frame(u).eps; earlier even field F' = standard(conj u), conj u = swap(oddBirthPrefix u);
  odd donor (N_c, D_c) = parents(conj)[0]; creator sign eps_c = Frame(conj).eps;
  shortShift sigma' = 2 eps_c (D_c, N_c); parentShift v = eps_c (N_c - D_c, N_c + D_c);
  primitive price P(z) = F'(z) - F'(z - v) - eps_c (N_c z1 - D_c z2);
  signed raw slip D_eta(z) = F'(z) - F'(z + eta sigma');  rounded slip J_eta = (D_eta + 1) // 2 (= ceil(D/2)).
  arrow c -> i: i is the lattice neighbour of c (even c: horizontal, odd c: vertical), i = c + step.
  admissible: P(i) <= P(c), D_eta(i) <= D_eta(c), J_eta(i) <= J_eta(c).
"""
import sys, itertools
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w3/scripts')
import permit_local as pl
from collections import Counter, defaultdict

def proper_words(maxlen=4):
    for L in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=L):
            if any(x != 3 for x in w):
                yield tuple(w)

def is_even(z):
    return (z[0] + z[1]) % 2 == 0

def nbr_ok(c, i):
    d = (i[0] - c[0], i[1] - c[1])
    return d in (((1, 0), (-1, 0)) if is_even(c) else ((0, 1), (0, -1)))

def setup(u, sigma_mode='corrected', round_mode='eta'):
    u = list(u)
    eta = pl.Frame(u).eps
    conj = tuple(pl.swap(pl.odd_birth_prefix(u)))
    F = pl.standard(conj)[0]
    epsc = pl.Frame(list(conj)).eps
    (Nc, Dc), _ = pl.parents(list(conj))[0], None
    if sigma_mode == 'corrected':
        sig = (2 * epsc * Dc, 2 * epsc * Nc)
    else:  # objection: (2 eta D, 2 eta N), no creator sign
        sig = (2 * eta * Dc, 2 * eta * Nc)
    par = (epsc * (Nc - Dc), epsc * (Nc + Dc))
    def P(z):
        return F(z) - F((z[0] - par[0], z[1] - par[1])) - epsc * (Nc * z[0] - Dc * z[1])
    def Draw(e, z):
        return F(z) - F((z[0] + e * sig[0], z[1] + e * sig[1]))
    def Jr(e, z):
        return (Draw(e, z) + 1) // 2
    return dict(u=tuple(u), eta=eta, conj=conj, F=F, epsc=epsc, Nc=Nc, Dc=Dc, sig=sig, P=P, D=Draw, J=Jr,
                round_mode=round_mode)

def arrows_for(eta, north_both=False):
    arr = [('V0 east', (0, 0), (1, 0))]
    if eta == 1:
        arr.append(('V1 south', (0, 1), (0, 0)))
    else:
        arr.append(('Vm1 west', (1, -1), (0, -1)))
        arr.append(('Hlast-U north', (0, -1), (0, 0)))
    if north_both and eta == 1:
        arr.append(('Hlast-U north (eta+)', (0, -1), (0, 0)))
    return arr

def check_arrow(S, eta_arrow_sign, c, i, round_mode):
    e = eta_arrow_sign
    Jf = (lambda z: S['J'](e, z)) if round_mode == 'eta' else (lambda z: S['J'](1, z))
    dP = S['P'](i) - S['P'](c)
    dD = S['D'](e, i) - S['D'](e, c)
    dJ = Jf(i) - Jf(c)
    return (dP <= 0 and dD <= 0 and dJ <= 0), (dP, dD, dJ)

def run(sigma_mode='corrected', round_mode='eta', north_both=False, verbose=False):
    per_len = defaultdict(Counter)
    fails = []
    words = list(proper_words(4))
    for u in words:
        S = setup(u, sigma_mode, round_mode)
        eta = S['eta']
        assert eta in (1, -1)
        for name, c, i in arrows_for(eta, north_both):
            assert nbr_ok(c, i), (u, name)
            ok, deltas = check_arrow(S, eta, c, i, round_mode)
            L = len(u)
            per_len[L]['arrows'] += 1
            per_len[L]['admissible' if ok else 'FAIL'] += 1
            if not ok:
                fails.append((u, S['conj'], eta, name, deltas))
    return words, per_len, fails

if __name__ == '__main__':
    north_both = 'both' in sys.argv[1:]
    words, per_len, fails = run(sigma_mode='corrected', round_mode='eta', north_both=north_both)
    print('words:', len(words))
    tot = Counter()
    for L in sorted(per_len):
        print('len', L, dict(per_len[L]))
        tot.update(per_len[L])
    print('TOTAL', dict(tot))
    print('fails:', len(fails))
    for f in fails[:20]:
        print('  ', f)
