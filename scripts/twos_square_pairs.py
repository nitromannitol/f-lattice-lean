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


def piece_of(a, w):
    """the charge branch of the native point w: 'E' (even quarter turn) or the OddWhite piece that holds."""
    from twos_square_lean import PIECES, piece_holds
    X, Y = 2 * a - w[1], w[0] + 1
    if (X + Y) % 2 == 0:
        return 'E'
    pc = [p for p in PIECES if piece_holds(p, X, Y, a)]
    return pc[0] if pc else 'NONE'


def pref_copy(A, v):
    """the native copy used by the generator: v itself if native, else the first native copy in the window."""
    from twos_square_rules import native_copy
    w, lam = native_copy(A, v)
    return w, lam


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
                lab_nf = r  # (e, lam, d)
                break
        if lab_nf is not None:
            e, lam, d = lab_nf
            v = (u[0] + e[0], u[1] + e[1])
            w = (v[0] - lam[0] * (A + 1) + 2 * lam[1], v[1] - lam[0] * (A - 1) - 2 * A * lam[1])
            lab = '%s;%s' % (str(lab_nf), piece_of(A, w))
            lab = (lab, lab)
        else:
            labs = []
            for eta in (1, -1):
                ws = witnesses_free(t, A, forced, u, eta)
                ws = sorted(ws)
                if not ws:
                    labs.append('NONE')
                    continue
                e, lam_h, d = ws[0]
                v = (u[0] + e[0], u[1] + e[1])
                w, lam_w = pref_copy(A, v)
                labs.append('F%s;%s;%s' % (str((e, lam_h, d)), str(lam_w), piece_of(A, w) if w else 'NONE'))
            lab = (labs[0], labs[1])
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
