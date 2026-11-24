"""Free-class witnesses of the square clause on the free leaves of the decision tree (twos signed policy).
For a free leaf square u and a sign eta: a corner v of S(u) with lap(v) = 0, v in a free class, whose retained input
v + dirs_eta(v) leaves S(u). The free alias h = v - lam of v (an H or V site in the lattice window) fixes the table entry.
The output lists, per free leaf and sign, the witness tuples (corner, lam, displacement) and whether they are uniform."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import natural, HV  # noqa: E402

CORNERS = [(0, 0), (1, 0), (0, 1), (1, 1)]


def free_alias(A, v):
    U = (A + 1, A - 1)
    V = (-2, 2 * A)
    for i in range(-3, 4):
        for l in range(-3, 4):
            h = (v[0] - i * U[0] - l * V[0], v[1] - i * U[1] - l * V[1])
            H, Vv = HV(A, *h)
            if H or Vv:
                return h, (i, l)
    return None, None


def witnesses_free(t, A, forced, u, eta):
    x, y = u
    S = {(x, y), (x + 1, y), (x, y + 1), (x + 1, y + 1)}
    dirs = t.dirs(eta, forced)
    out = []
    for e in CORNERS:
        v = (x + e[0], y + e[1])
        if t.lap(v) != 0:
            continue
        h, lam = free_alias(A, v)
        if h is None:
            continue
        R = t.retained(dirs, v)
        if R is None or set(R) <= S:
            continue
        d = (dirs[t.key(v)][0], dirs[t.key(v)][1])
        out.append((e, lam, d))
    return out


if __name__ == '__main__':
    from twos_square_lean import dataset as _unused  # noqa: F401  (keeps the same leaf ids as the generator)
    from twos_square_leaves import dataset, KEYS
    import numpy as np
    from sklearn.tree import DecisionTreeClassifier
    train_K = (2, 3, 4, 5)
    train = sum([dataset(K) for K in train_K], [])
    X = np.array([[f[k] for k in KEYS] for f, _, _ in train])
    yl = np.array([l for _, l, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    free_nodes = [n for n in range(clf.tree_.node_count) if clf.tree_.children_left[n] == -1 and
                  clf.classes_[int(np.argmax(clf.tree_.value[n][0]))] == 'FREE']
    for K in train_K:
        pass
    result = {}
    for node in free_nodes:
        per_eta = {1: Counter(), -1: Counter()}
        missing = {1: 0, -1: 0}
        n_samples = 0
        for K in train_K:
            t = Twos(K)
            A = t.a
            forced, _ = t.forced(t.clauses())
            ds = dataset(K)
            Xk = np.array([[f[k] for k in KEYS] for f, _, _ in ds])
            ids = clf.apply(Xk)
            for (f, l, u), nid in zip(ds, ids):
                if nid != node:
                    continue
                n_samples += 1
                for eta in (1, -1):
                    ws = witnesses_free(t, A, forced, u, eta)
                    if not ws:
                        missing[eta] += 1
                    for w in ws:
                        per_eta[eta][w] += 1
        result[node] = (n_samples, missing, per_eta)
        print('free leaf', node, 'samples', n_samples, 'missing witnesses (eta=+1,-1):', missing[1], missing[-1])
        for eta in (1, -1):
            print('    eta=%+d witnesses (corner, lam, disp): %s' % (eta, dict(per_eta[eta].most_common(6))))
