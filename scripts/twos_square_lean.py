"""Writes the Lean leaves of the square-witness decision tree (FLatticePaper/Plane/Induction/TwosSquareLeaves.lean).

The tree is the one of twos_square_leaves.py (features x, x-a, y, y-a, y-2a, t, t-a, t-2a, parity; a = 2k+4). Each non-FREE
leaf is one theorem: its region hypotheses; the corner v = (x+e1, y+e2); its native copy w = v - (i U + l V); the white charge
(the parity branch of the quarter turn of w, and for the odd branch the piece of OddWhite that holds on the leaf, both computed
numerically for the leaf and checked by omega); the non-free native test; the candidate guard (one alternative, chosen by the
tactic `first`); the candidate direction d; and the outside test. The free leaves are listed for the next block."""
import ast
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_square_leaves import dataset, KEYS  # noqa: E402
import numpy as np  # noqa: E402
from sklearn.tree import DecisionTreeClassifier  # noqa: E402

A = '(2 * (k : ℤ) + 4)'
FEAT = {'x': 'x', 'xa': f'(x - {A})', 'y': 'y', 'ya': f'(y - {A})', 'y2a': f'(y - 2 * {A})',
        't': '(y - x)', 'ta': f'(y - x - {A})', 't2a': f'(y - x - 2 * {A})', 'par': '((x + y) % 2)'}
PIECES = ['LB1', 'LB2', 'LB3', 'LB1r', 'LB2r', 'LB3r', 'OW3', 'OW4', 'OW5', 'OW6']
# selector term for each piece inside LadderOddOddWhite (= LB ∨ (LB' ∨ (OW3 ∨ (OW4 ∨ (OW5 ∨ OW6)))))
SEL = {'LB1': 'Or.inl (Or.inl {h})', 'LB2': 'Or.inl (Or.inr (Or.inl {h}))', 'LB3': 'Or.inl (Or.inr (Or.inr {h}))',
       'LB1r': 'Or.inr (Or.inl (Or.inl {h}))', 'LB2r': 'Or.inr (Or.inl (Or.inr (Or.inl {h})))',
       'LB3r': 'Or.inr (Or.inl (Or.inr (Or.inr {h})))', 'OW3': 'Or.inr (Or.inr (Or.inl {h}))',
       'OW4': 'Or.inr (Or.inr (Or.inr (Or.inl {h})))', 'OW5': 'Or.inr (Or.inr (Or.inr (Or.inr (Or.inl {h}))))',
       'OW6': 'Or.inr (Or.inr (Or.inr (Or.inr (Or.inr {h}))))'}


def piece_holds(name, X, Y, a):
    """the pieces of LadderOddOddWhite at the point (X, Y) with den = a (X = 2a - w2, Y = w1 + 1)."""
    R = (a + 2 - X, a + 2 - Y)
    def LB(p):
        return [p[0] + p[1] == 1 and 2 - a <= p[0] <= -1, p[1] == 0 and 1 <= p[0] <= a - 1, p[1] == 1 and a <= p[0] <= 2 * a]
    if name in ('LB1', 'LB2', 'LB3'):
        return LB((X, Y))[int(name[2]) - 1]
    if name in ('LB1r', 'LB2r', 'LB3r'):
        return LB(R)[int(name[2]) - 1]
    if name == 'OW3':
        return X + Y == a + 1 and 1 <= Y <= a - 1
    if name == 'OW4':
        return X + Y == a + 3 and 3 <= Y <= a + 1
    if name == 'OW5':
        return X == 0 and Y == 1
    return X == a + 2 and Y == a + 1


def leaves(clf):
    tr = clf.tree_
    out = []

    def walk(node, path):
        if tr.children_left[node] == -1:
            out.append((node, path, clf.classes_[int(np.argmax(tr.value[node][0]))]))
            return
        f = KEYS[tr.feature[node]]
        th = tr.threshold[node]
        walk(tr.children_left[node], path + [(f, '<=', th)])
        walk(tr.children_right[node], path + [(f, '>', th)])
    walk(0, [])
    return out


def cond_lean(f, op, th):
    c = int(np.floor(th))
    if f == 'par':
        return '(x + y) % 2 = 0' if op == '<=' else '(x + y) % 2 = 1'
    if op == '<=':
        return f'{FEAT[f]} ≤ {c}'
    return f'{c + 1} ≤ {FEAT[f]}'


def leaf_data(samples, lab, K):
    """the parity branch, the odd OddWhite pieces, and the candidate band of the corner's native copy (uniform per leaf)."""
    e, lam, d = ast.literal_eval(lab)
    i, l = lam
    a = 2 * K + 2  # Twos(K).a; the Lean parameter is a = 2k+4 with k = K-1
    branches, pieces, bands = set(), set(), set()
    for u in samples:
        x, y = u
        v = (x + e[0], y + e[1])
        w = (v[0] - i * (a + 1) + 2 * l, v[1] - i * (a - 1) - 2 * a * l)
        X, Y = 2 * a - w[1], w[0] + 1
        even_rot = (X + Y) % 2 == 0
        branches.add(even_rot)
        if not even_rot:
            pc = [p for p in PIECES if piece_holds(p, X, Y, a)]
            pieces.add(pc[0] if pc else 'NONE')
        if tuple(d) in ((1, 0),):
            bands.add('E')
        elif tuple(d) in ((-1, 0),):
            bands.add('W')
        else:
            tw = w[1] - w[0]
            low = (w[1] - w[0]) % 2 == 1 and -1 <= tw <= a - 3
            bands.add('low' if low else 'high')
    return branches, pieces, bands


def leaf_text(idx, path, lab, branches, pieces, bands):
    e, lam, d = ast.literal_eval(lab)
    i, l = lam
    v1 = f'x + {e[0]}' if e[0] else 'x'
    v2 = f'y + {e[1]}' if e[1] else 'y'
    w1 = f'({v1}) - {i} * ({A} + 1) + 2 * {l}'
    w2 = f'({v2}) - {i} * ({A} - 1) - 2 * {A} * {l}'
    conds = [cond_lean(f, op, th) for f, op, th in path]
    hyps = '\n'.join(f'    (_c{j} : {c})' for j, c in enumerate(conds))
    corner_pick = {(0, 0): 'Or.inl rfl', (1, 0): 'Or.inr (Or.inl rfl)', (0, 1): 'Or.inr (Or.inr (Or.inl rfl))',
                   (1, 1): 'Or.inr (Or.inr (Or.inr rfl))'}[tuple(e)]
    if len(branches) != 1 or 'NONE' in pieces or len(bands) != 1:
        raise ValueError('leaf %d not uniform: branches %s pieces %s bands %s' % (idx, branches, pieces, bands))
    even_rot = next(iter(branches))
    EV = f'EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2}))'
    if even_rot:
        charge = f'''    by_cases he : {EV}
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega'''
    else:
        alts = []
        for pc in sorted(pieces):
            sel = SEL[pc].replace('{h}', '?_')
            alts.append(f'      | (refine {sel}; omega)')
        charge = f'''    by_cases he : {EV}
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
    · refine Or.inr ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd] at he ⊢
      first
''' + '\n'.join(alts)
    band = next(iter(bands))
    AA = '(2 * (k : ℤ) + 4)'
    W1, W2 = f'({w1})', f'({w2})'
    cutoff_low = f'{AA} - 1'
    cutoff_high = f'2 * {AA} - 1'
    if band == 'E':
        guard_text = '    refine Or.inr (Or.inr (Or.inl ?_))\n    simp only [CandE]\n    omega'
        hd_text = f'    exact candDisp_E (by simp only [CandE]; omega)'
    elif band == 'W':
        guard_text = '    refine Or.inr (Or.inr (Or.inr ?_))\n    simp only [CandW]\n    omega'
        hd_text = f'    exact candDisp_W (by simp only [CandW]; omega)'
    elif band == 'low':
        guard_text = '    refine Or.inl ?_\n    simp only [CandLow]\n    omega'
        if d[1] == -1:
            hd_text = f'    exact candDisp_low_down (by simp only [CandLow]; omega) (by omega)'
        else:
            hd_text = f'    exact candDisp_low_up (by simp only [CandLow]; omega) (by omega)'
    else:
        guard_text = '    refine Or.inr (Or.inl ?_)\n    simp only [CandHigh]\n    omega'
        if d[1] == -1:
            hd_text = f'    exact candDisp_high_down (by simp only [CandHigh]; omega) (by omega)'
        else:
            hd_text = f'    exact candDisp_high_up (by simp only [CandHigh]; omega) (by omega)'
    txt = f'''set_option maxHeartbeats 400000 in
theorem sq_leaf_{idx} (k : ℕ) {{S : Field}}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
{hyps} :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) ({v1}, {v2}) := by
    unfold SqCorner
    exact {corner_pick}
  have hw : AliasOf (2 * (k : ℤ) + 4) ({v1}, {v2}) ({w1}, {w2}) :=
    ⟨{i}, {l}, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ({w1}) ({w2}) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2})) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2}))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2})) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2}))) := by
{charge}
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ({w1}) ({w2}) ∨
      FreeSite (2 * (k : ℤ) + 4) (({w1}) + 2) (({w2}) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (({w1}) - ((2 * (k : ℤ) + 4) + 1)) (({w2}) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ({w1}) ({w2}) := by
{guard_text}
  have hd : candDisp (2 * (k : ℤ) + 4) ({w1}) ({w2}) = ({d[0]}, {d[1]}) := by
{hd_text}
  have hout : SqOut (x, y) (({v1}) + {d[0]}, ({v2}) + {d[1]}) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)
'''
    return txt


if __name__ == '__main__':
    train_K = (2, 3, 4, 5)
    train = sum([dataset(K) for K in train_K], [])
    X = np.array([[f[k] for k in KEYS] for f, _, _ in train])
    yl = np.array([l for _, l, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    leaf_ids = clf.apply(X)
    L = leaves(clf)
    body = ['import FLatticePaper.Plane.Induction.TwosSquares', '',
            'namespace FLatticePaper.TwosEPolicy', 'open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey',
            '']
    nf = fr = 0
    free_ids = []
    for node, path, lab in L:
        if lab == 'FREE':
            free_ids.append(node)
            fr += 1
            continue
        samples = [(u, K) for K in train_K for (f, l, u) in dataset(K) if False]  # placeholder, replaced below
        # gather the samples of this leaf over all training K
        sel_u = []
        for K in train_K:
            ds = dataset(K)
            Xk = np.array([[f[k] for k in KEYS] for f, _, _ in ds])
            ids = clf.apply(Xk)
            for (f, l, u), nid in zip(ds, ids):
                if nid == node:
                    sel_u.append((u, K))
        branches = set()
        pieces = set()
        bands = set()
        for u, K in sel_u:
            b, p, bd = leaf_data([u], lab, K)
            branches |= b
            pieces |= p
            bands |= bd
        body.append(leaf_text(node, path, lab, branches, pieces, bands))
        nf += 1
    body.append('end FLatticePaper.TwosEPolicy')
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'FLatticePaper', 'Plane', 'Induction',
                       'TwosSquareLeaves.lean')
    open(out, 'w').write('\n'.join(body) + '\n')
    print('non-free leaves written', nf, '; free leaves pending', fr, 'ids', free_ids)
