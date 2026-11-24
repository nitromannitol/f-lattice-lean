"""Checks each leaf region of the pair-label square tree against larger values of K (not used to fit the tree): a native
lower-left square satisfying the path of a leaf must carry the leaf's label. Prints the leaves with mismatches."""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
from sklearn.tree import DecisionTreeClassifier  # noqa: E402
from twos_square_pairs import pair_labels  # noqa: E402
from twos_square_leaves import KEYS  # noqa: E402
from twos_square_lean import leaves, cond_lean  # noqa: E402


def holds(path, f):
    for feat, op, th in path:
        v = f[feat]
        if feat == 'par':
            ok = (v == 0) if op == '<=' else (v == 1)
        else:
            ok = (v <= th) if op == '<=' else (v > th)
        if not ok:
            return False
    return True


if __name__ == '__main__':
    train = []
    for K in (2, 3, 4, 5):
        train += pair_labels(K)
    X = np.array([[f[k] for k in KEYS] for f, _, _, _ in train])
    yl = np.array([l for _, l, _, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    L = leaves(clf)
    bad = Counter()
    checked = Counter()
    for K in range(6, 13):
        for f, lab, u, KK in pair_labels(K):
            for node, path, cls in L:
                if holds(path, f):
                    checked[node] += 1
                    if lab != cls:
                        bad[node] += 1
    for node, path, cls in L:
        flag = 'OK ' if bad[node] == 0 else 'BAD'
        print(flag, 'leaf', node, 'checked', checked[node], 'mismatches', bad[node], 'label', cls[:60])
