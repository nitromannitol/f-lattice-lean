"""Corner rules of the square clause on the native lower-left squares (twos signed policy, numerical check).
R(e) for a corner e in {(0,0),(1,0),(0,1),(1,1)} of S(u): the native corner v = u + e has lap 0, is non-free (the local test
of freeClass_native_iff), has CandGuard, and its candidate input v + candDir(v) leaves S(u). The coverage of the native
lower-left squares by R(0,0) or R(1,0) or R(0,1) or R(1,1), and the exception set Free(u) (the squares needing a free witness)."""
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural, HV, candidate  # noqa: E402

CORNERS = [(0, 0), (1, 0), (0, 1), (1, 1)]


def native_copy(A, v):
    """a native lattice copy of v, with the offset lambda = (i, l) (v = w + i U + l V), searched in a window."""
    U = (A + 1, A - 1)
    V = (-2, 2 * A)
    for i in range(-3, 4):
        for l in range(-3, 4):
            w = (v[0] - i * U[0] - l * V[0], v[1] - i * U[1] - l * V[1])
            if natural(A, *w):
                return w, (i, l)
    return None, None


def rule(t, A, u, e):
    x, y = u
    v = (x + e[0], y + e[1])
    if t.lap(v) != 0:
        return False
    w, lam = native_copy(A, v)
    if w is None:
        return False
    H, V = HV(A, *v)
    if H or V:
        return False
    for z in [(v[0] + 2, v[1] - 2 * A), (v[0] - (A + 1), v[1] - (A - 1))]:
        Hz, Vz = HV(A, *z)
        if Hz or Vz:
            return False
    g, (dx, dy) = candidate(A, *w)
    if not g:
        return False
    S = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
    return (v[0] + dx, v[1] + dy) not in S


if __name__ == '__main__':
    for K in [int(a) for a in sys.argv[1:]] or [3, 4]:
        t = Twos(K)
        A = t.a
        native = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
        exc = []
        used = defaultdict(int)
        for u in native:
            ok = [e for e in CORNERS if rule(t, A, u, e)]
            if not ok:
                exc.append(u)
            for e in ok:
                used[e] += 1
        print('K=%d a=%d: native lower-left squares %d, not covered by the four corner rules: %d, corner use %s'
              % (K, A, len(native), len(exc), dict(used)))
        print('   exceptions (x, t=y-x):', sorted((u[0], u[1] - u[0]) for u in exc))
