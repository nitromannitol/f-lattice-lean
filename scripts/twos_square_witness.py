"""Square-clause witnesses of the twos signed policy on the native lower-left squares (K = 1..4, both signs).
A witness is a corner v of S(u) = {u, u+(1,0), u+(0,1), u+(1,1)} with lap(v) = 0 whose retained input leaves S(u).
Corners outside the native box are reduced to their native lattice copy w = v - lambda (lambda in the lattice, found by the
window of nine aliases, all of which are checked to contain a copy). The table lists, per native u, the witnesses by
(corner, nonfree/free, copy offset), for each sign."""
import os
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural, HV  # noqa: E402


def native_copy(t, A, v):
    U = (A + 1, A - 1)
    V = (-2, 2 * A)
    for i in range(-3, 4):
        for l in range(-3, 4):
            w = (v[0] - i * U[0] - l * V[0], v[1] - i * U[1] - l * V[1])
            if natural(A, *w):
                return w, (i, l)
    return None, None


def witnesses(K, eta_list=(1, -1)):
    t = Twos(K)
    A = t.a
    forced, _ = t.forced(t.clauses())
    native = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    out = {}
    for eta in eta_list:
        dirs = t.dirs(eta, forced)
        for u in native:
            x, y = u
            S = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
            wit = []
            for e in [(0, 0), (1, 0), (0, 1), (1, 1)]:
                v = (x + e[0], y + e[1])
                if t.lap(v) != 0:
                    continue
                R = t.retained(dirs, v)
                if R is None or set(R) <= S:
                    continue
                w, lam = native_copy(t, A, v)
                H, Vv = HV(A, *v)
                wit.append((e, 'free' if (H or Vv) else 'nonfree', lam))
            out[(eta, u)] = wit
    return t, native, out


if __name__ == '__main__':
    for K in [int(a) for a in sys.argv[1:]] or [3, 4]:
        t, native, out = witnesses(K)
        A = t.a
        nonfree_both = sum(1 for u in native if any(k == 'nonfree' for _, k, _ in out[(1, u)]) and any(k == 'nonfree' for _, k, _ in out[(-1, u)]))
        print('K=%d a=%d: native squares %d, with a nonfree witness for both signs: %d' % (K, A, len(native), nonfree_both))
        missing_copy = sum(1 for k2, ws in out.items() for (_, _, lam) in ws if lam is None)
        print('   witnesses without a native copy in the window: %d' % missing_copy)
