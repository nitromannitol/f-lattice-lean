"""A deck-periodic version of the archive's pure-2 rank (twos_archive_rank.py). Each key class of the twos period lattice
gets the value of deckrank at its lexicographically smallest native copy, so the rank is periodic by construction.
Checks for K = 1..4 and both signs, over all selected edges of one native copy per class (the policy and both prices
are periodic, so this covers all edges):
  (a) strict on Phi-flat selected edges: rho(i) < rho(c);
  (b) Phi-drop edges: the variation of rho stays below the Phi weight M = 2d+3, so R = M*Phi + rho is strict on every edge.
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural, deckrank  # noqa: E402


def check(K):
    t = Twos(K)
    A = t.a
    forced, _ = t.forced(t.clauses())
    pts = sorted((x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y))
    lexmin = {}
    for p in pts:
        lexmin.setdefault(t.key(p), p)
    assert len(lexmin) == t.T

    def rho(z):
        return deckrank(A, *lexmin[t.key(z)], )  # placeholder, replaced below

    out = Counter()
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)

        def rho(z, eta=eta):
            return deckrank(A, lexmin[t.key(z)][0], lexmin[t.key(z)][1], eta)
        for k in range(t.T):
            c = t.rep(k)
            # use the native copy of class k as the centre, and its retained inputs
            cc = lexmin[t.key(c)] if False else None
        for p in lexmin.values():
            for i in t.retained(dirs, p):
                dphi = t.chain(eta, i) - t.chain(eta, p)
                dr = rho(i) - rho(p)
                out[('edges', eta)] += 1
                if dphi == 0 and not dr < 0:
                    out[('flat_bad', eta)] += 1
                if dphi < 0:
                    out[('drop', eta)] += 1
                    if dr >= 2 * t.d + 3 + 0 and False:
                        pass
                out[('max_var', eta)] = max(out[('max_var', eta)], abs(dr))
                if dphi < 0 and dr >= (2 * t.d + 3) * (-dphi):
                    out[('weight_bad', eta)] += 1
        out[('rho_range', eta)] = (min(rho(p) for p in lexmin.values()), max(rho(p) for p in lexmin.values()))
    return t, out


if __name__ == '__main__':
    for K in [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4]:
        t, out = check(K)
        for eta in (1, -1):
            print('K=%d eta=%+d edges %d  Phi-flat non-strict %d  Phi-drop edges %d  weight failures (M=2d+3=%d) %d  '
                  'max |variation| %d  rho range %s'
                  % (K, eta, out[('edges', eta)], out[('flat_bad', eta)], out[('drop', eta)], 2 * t.d + 3,
                     out[('weight_bad', eta)], out[('max_var', eta)], out[('rho_range', eta)]))
