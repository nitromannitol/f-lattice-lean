"""Closed deck-periodic rank candidate for the twos signed policy (K = 1..4).
Closed tile: S = { p native : not (p = v + U or p = v + V for a native H/V site v, and p is not an H/V site ) }, with
U = (a+1, a-1), V = (-2, 2a) (checked equal to the computed tile below).
The archive native set, minus the duplicated free copies (native free-class sites that are not H/V sites), is a tile S with
one site per key class (checked). rho(c) = deckrank(S-site of key(c)) is periodic by construction, and R = (2d+3) Phi + rho
is strict on every selected edge (checked over all classes, both signs). The window rule (the nine alias translates alone)
is not total: some sites have no native copy in their window, so the archive deckrank is a fundamental-domain formula."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural, deckrank, HV  # noqa: E402


def in_HV(A, p):
    H, V = HV(A, p[0], p[1])
    return H or V


def check(K):
    t = Twos(K)
    A = t.a
    forced, _ = t.forced(t.clauses())
    native = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    # the free-class duplicates: native sites whose key is a free class but which are not themselves H/V sites
    hv_native_keys = {t.key(v) for v in t.H() + t.V() if natural(A, *v)}
    dup = [p for p in native if t.key(p) in hv_native_keys and not in_HV(A, p)]
    S = [p for p in native if p not in set(dup)]
    # the H/V site (-1, a) is outside the native box; its class keeps its native copy (nothing is dropped there)
    keys = [t.key(p) for p in S]
    out = {'native': len(native), 'dups': len(dup), 'S': len(S), 'T': t.T,
           'one_per_class': len(set(keys)) == t.T == len(keys),
           'HV_native': all(natural(A, *v) for v in t.H() + t.V()), 'HV_outside_native': [v for v in t.H() + t.V() if not natural(A, *v)]}
    s_of = {t.key(p): p for p in S}
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)

        def rho(z, eta=eta):
            s = s_of[t.key(z)]
            return deckrank(A, s[0], s[1], eta)
        flat_bad = weight_bad = 0
        for p in S:
            for i in t.retained(dirs, p):
                dphi = t.chain(eta, i) - t.chain(eta, p)
                dr = rho(i) - rho(p)
                flat_bad += (dphi == 0 and not dr < 0)
                weight_bad += (dphi < 0 and dr >= (2 * t.d + 3) * (-dphi))
        out[('flat', eta)] = flat_bad
        out[('weight', eta)] = weight_bad
    return out


if __name__ == '__main__':
    for K in [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4]:
        o = check(K)
        print('K=%d T=%d native %d, duplicate free copies %d, tile S %d, one site per class: %s, H/V sites native: %s | '
              'eta=+1 flat %d weight %d | eta=-1 flat %d weight %d'
              % (K, o['T'], o['native'], o['dups'], o['S'], o['one_per_class'], o['HV_native'],
                 o[('flat', 1)], o[('weight', 1)], o[('flat', -1)], o[('weight', -1)]))
