"""Pair-label decision tree for the square clause (twos signed policy).
For a native lower-left square u and each sign eta: the label L_eta(u) is the non-free witness (corner, lattice copy offset,
candidate direction) when a non-free corner rule holds (sign independent), else the free witness (corner, H/V alias offset,
retained displacement) for eta. The pair (L_+1, L_-1) labels the square; the tree is fitted on K = 2..5 and checked on K = 6, 7."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos, add  # noqa: E402
from twos_archive_rank import natural, HV, candidate  # noqa: E402
from twos_square_leaves import dataset, KEYS, corner_label, ORDER  # noqa: E402
from twos_square_free import witnesses_free, free_alias  # noqa: E402


def pair_labels(K):
    t = Twos(K)
    A = t.a
    forced, _ = t.forced(t.clauses())
    native = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    out = []
    for u in native:
        lab_nf = None
        for e in ORDER:
            r = corner_label(t, A, u, e)
            if r is not None:
                lab_nf = str(r)
                break
        if lab_nf is not None:
            lab = (lab_nf, lab_nf)
        else:
            labs = []
            for eta in (1, -1):
                ws = witnesses_free(t, A, forced, u, eta)
                labs.append(str(sorted(ws)[0]) if ws else 'NONE')
            lab = ('F' + labs[0], 'F' + labs[1])
        x, y = u
        ta = y - x
        f = dict(x=x, xa=x - A, y=y, ya=y - A, y2a=y - 2 * A, t=ta, ta=ta - A, t2a=ta - 2 * A, par=(x + y) % 2)
        out.append((f, '|'.join(lab), u, K))
    return out


if __name__ == '__main__':
    from sklearn.tree import DecisionTreeClassifier, export_text
    import numpy as np
    train = []
    for K in (2, 3, 4, 5):
        train += pair_labels(K)
    X = np.array([[f[k] for k in KEYS] for f, _, _, _ in train])
    yl = np.array([l for _, l, _, _ in train])
    print('label counts (top):', Counter(yl).most_common(12))
    print('NONE labels:', sum(1 for l in yl if 'NONE' in l))
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    for K in (6, 7):
        te = pair_labels(K)
        Xt = np.array([[f[k] for k in KEYS] for f, _, _, _ in te])
        yt = np.array([l for _, l, _, _ in te])
        print('K=%d held-out accuracy %.3f, leaves %d' % (K, (clf.predict(Xt) == yt).mean(), clf.get_n_leaves()))
