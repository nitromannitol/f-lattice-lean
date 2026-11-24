"""Leaves of the square-witness decision tree (twos signed policy, non-free corners).
Label of a native lower-left square u: (corner e, lattice offset lam of the native copy w of the corner, candidate direction
d of w) for the first valid corner in ORDER, or FREE. The decision tree on the features x, x-a, y, y-a, y-2a, t, t-a, t-2a,
parity (t = y - x) is fitted on K = 2..5 and checked on K = 6, 7 (see the printed accuracy)."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural, HV, candidate  # noqa: E402
from twos_square_rules import native_copy  # noqa: E402

ORDER = [(1, 0), (0, 0), (0, 1), (1, 1)]
KEYS = ['x', 'xa', 'y', 'ya', 'y2a', 't', 'ta', 't2a', 'par']


def corner_label(t, A, u, e):
    x, y = u
    v = (x + e[0], y + e[1])
    if t.lap(v) != 0:
        return None
    w, lam = native_copy(A, v)
    if w is None:
        return None
    H, V = HV(A, *v)
    if H or V:
        return None
    for z in [(v[0] + 2, v[1] - 2 * A), (v[0] - (A + 1), v[1] - (A - 1))]:
        Hz, Vz = HV(A, *z)
        if Hz or Vz:
            return None
    g, d = candidate(A, *w)
    if not g:
        return None
    S = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
    if (v[0] + d[0], v[1] + d[1]) in S:
        return None
    return (e, lam, d)


def dataset(K):
    t = Twos(K)
    A = t.a
    native = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    out = []
    for u in native:
        lab = 'FREE'
        for e in ORDER:
            r = corner_label(t, A, u, e)
            if r is not None:
                lab = str(r)
                break
        x, y = u
        ta = y - x
        f = dict(x=x, xa=x - A, y=y, ya=y - A, y2a=y - 2 * A, t=ta, ta=ta - A, t2a=ta - 2 * A, par=(x + y) % 2)
        out.append((f, lab, u))
    return out


if __name__ == '__main__':
    from sklearn.tree import DecisionTreeClassifier, export_text
    import numpy as np
    train = sum([dataset(K) for K in (2, 3, 4, 5)], [])
    X = np.array([[f[k] for k in KEYS] for f, _, _ in train])
    yl = np.array([l for _, l, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    for K in (6, 7):
        te = dataset(K)
        Xt = np.array([[f[k] for k in KEYS] for f, _, _ in te])
        yt = np.array([l for _, l, _ in te])
        print('K=%d held-out accuracy %.3f, leaves %d' % (K, (clf.predict(Xt) == yt).mean(), clf.get_n_leaves()))
    print(Counter(l for _, l, _ in train))
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '.work', 'square_tree.txt'), 'w').write(
        export_text(clf, feature_names=KEYS, max_depth=40))
