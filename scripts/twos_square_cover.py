"""Writes the coverage theorem of the square clause for the native lower-left squares (twos signed policy): the nested
dispatch over the pair-label tree (scripts/twos_square_pairs.py), with one leaf theorem per leaf (sq_leaf_<n>, in
TwosSquareLeaves.lean). Leaves that are free (generic in the sign or split by it) take hη; non-free leaves do not."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402
from sklearn.tree import DecisionTreeClassifier  # noqa: E402
from twos_square_pairs import pair_labels  # noqa: E402
from twos_square_leaves import KEYS  # noqa: E402
from twos_square_lean import FEAT  # noqa: E402
from twos_square_lean2 import leaf_free_text  # noqa: E402,F401  (same leaf kinds as the generator)

A = '(2 * (k : ℤ) + 4)'


def split_prop(feat, th):
    c = int(np.floor(th))
    if feat == 'par':
        return '(x + y) % 2 = 0'
    return f'{FEAT[feat]} ≤ {c}'


def gen(tr, node, leaf_kind, leaf_conds, indent, out):
    pad = ' ' * indent
    if tr.children_left[node] == -1:
        kind = leaf_kind[node]
        omegas = ' '.join('(by omega)' for _ in leaf_conds[node])
        if kind == 'free':
            out.append(f'{pad}exact sq_leaf_{node} k hagree hperiod η hη x y hu {omegas}')
        else:
            out.append(f'{pad}exact sq_leaf_{node} k hagree hperiod η x y hu {omegas}')
        return
    feat = KEYS[tr.feature[node]]
    th = tr.threshold[node]
    out.append(f'{pad}by_cases h{node} : {split_prop(feat, th)}')
    for child in (tr.children_left[node], tr.children_right[node]):
        sub = []
        gen(tr, child, leaf_kind, leaf_conds, indent + 2, sub)
        sub[0] = pad + '· ' + sub[0].lstrip()
        out.extend(sub)


if __name__ == '__main__':
    import ast
    from twos_square_lean import leaves
    train = []
    for K in (2, 3, 4, 5):
        train += pair_labels(K)
    X = np.array([[f[k] for k in KEYS] for f, _, _, _ in train])
    yl = np.array([l for _, l, _, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    tr = clf.tree_
    leaf_kind = {}
    leaf_conds = {}
    from twos_square_lean import cond_lean
    for node, path, cls in leaves(clf):
        leaf_kind[node] = 'free' if 'F' in cls else 'nonfree'
        leaf_conds[node] = [cond_lean(f, op, th) for f, op, th in path]
    body = ['import FLatticePaper.Plane.Induction.TwosSquareLeaves', '',
            'namespace FLatticePaper.TwosEPolicy', 'open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey',
            '', 'set_option maxHeartbeats 400000 in',
            'theorem sq_clause_native (k : ℕ) {S : Field}',
            '    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)',
            '    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))',
            '    (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (hu : NativeT (2 * (k : ℤ) + 4) x y) :',
            '    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by']
    gen(tr, 0, leaf_kind, leaf_conds, 2, body)
    body.append('end FLatticePaper.TwosEPolicy')
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'FLatticePaper', 'Plane', 'Induction',
                       'TwosSquareCover.lean')
    open(out, 'w').write('\n'.join(body) + '\n')
    print('cover written; leaves', sum(1 for n in range(tr.node_count) if tr.children_left[n] == -1))
