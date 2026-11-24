"""Decision tree for the square witnesses (twos signed policy, nonfree corners). Label of a native lower-left square u:
the first corner e (in the priority order below) with rule(e) true, or FREE. Features are linear in (x, y, a) so the
thresholds are symbolic in a. Fitted on K = 2..5, checked on K = 6."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural  # noqa: E402
from twos_square_rules import rule  # noqa: E402

ORDER = [(1, 0), (0, 0), (0, 1), (1, 1)]


def dataset(K):
    t = Twos(K)
    A = t.a
    native = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    rows = []
    for u in native:
        lab = 'FREE'
        for e in ORDER:
            if rule(t, A, u, e):
                lab = str(e)
                break
        x, y = u
        ta = y - x
        feats = dict(x=x, xa=x - A, y=y, ya=y - A, y2a=y - 2 * A, t=ta, ta=ta - A, t2a=ta - 2 * A,
                     par=(x + y) % 2)
        rows.append((feats, lab, A))
    return rows


if __name__ == '__main__':
    from sklearn.tree import DecisionTreeClassifier, export_text
    import numpy as np
    keys = ['x', 'xa', 'y', 'ya', 'y2a', 't', 'ta', 't2a', 'par']
    train = []
    for K in [2, 3, 4, 5]:
        train += dataset(K)
    test = dataset(6)
    X = np.array([[f[k] for k in keys] for f, _, _ in train])
    yl = np.array([l for _, l, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    print('train size', len(train), 'leaves', clf.get_n_leaves(), 'depth', clf.get_depth())
    Xt = np.array([[f[k] for k in keys] for f, _, _ in test])
    yt = np.array([l for _, l, _ in test])
    print('held-out K=6 accuracy:', (clf.predict(Xt) == yt).mean())
    print(export_text(clf, feature_names=keys, max_depth=30))
