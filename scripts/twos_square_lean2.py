"""Lean leaves of the pair-label square tree (twos signed policy). Regenerates
FLatticePaper/Plane/Induction/TwosSquareLeaves.lean from scripts/twos_square_pairs.py.

The tree is pure in the pair label, so every leaf has one label per sign. A non-free leaf (both labels non-free) is written as
in the single-label generator. A free leaf takes the hypothesis hη : η = 1 ∨ η = -1; when the two signs have the same
witness type the proof is generic in η, otherwise it splits (rcases hη with rfl | rfl) into two blocks with numeric η."""
import ast
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos  # noqa: E402
from twos_archive_rank import HV  # noqa: E402
from twos_square_pairs import pair_labels  # noqa: E402
from twos_square_leaves import KEYS  # noqa: E402
from twos_square_lean import cond_lean  # noqa: E402
from twos_square_rules import native_copy  # noqa: E402
from twos_square_lean import leaves, SEL, PIECES, piece_holds, leaf_text  # noqa: E402
import numpy as np  # noqa: E402
from sklearn.tree import DecisionTreeClassifier  # noqa: E402

TRAIN_K = (2, 3, 4, 5)
AA = '(2 * (k : ℤ) + 4)'


def charge_of_point(w, a):
    """(even rot branch, odd OddWhite piece) of the native point w for den a."""
    X, Y = 2 * a - w[1], w[0] + 1
    even_rot = (X + Y) % 2 == 0
    piece = None
    if not even_rot:
        pc = [p for p in PIECES if piece_holds(p, X, Y, a)]
        piece = pc[0] if pc else 'NONE'
    return even_rot, piece


def charge_text(w1, w2, branches, pieces):
    EV = f'EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2}))'
    if len(branches) != 1 or 'NONE' in pieces:
        raise ValueError('charge not uniform %s %s' % (branches, pieces))
    if next(iter(branches)):
        return f'''    by_cases he : {EV}
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega'''
    alts = [f'      | (refine {SEL[pc].replace("{h}", "?_")}; omega)' for pc in sorted(pieces)]
    SUBS = ', Prod.fst_sub, Prod.snd_sub' if any(pc.endswith('r') for pc in pieces) else ''
    return f'''    by_cases he : {EV}
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
    · refine Or.inr ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd{SUBS}] at he ⊢
      first
''' + '\n'.join(alts)


def h_type(h, a):
    H, V = HV(a, *h)
    if h == (1, 0):
        return 'H0'
    if h == (0, 0):
        return 'V0'
    even = (h[0] + h[1]) % 2 == 0
    if H:
        return 'He' if even else 'Ho'
    if V:
        return 'Ve' if even else 'Vo'
    raise ValueError('not an H/V site %s' % (h,))


def D_FORMULA(typ, eta):
    return {'H0': (0, -eta), 'He': (1, 0), 'Ho': (0, 1), 'V0': (1, 0), 'Ve': (eta, 0), 'Vo': (0, -eta)}[typ]


def free_block(e, lam_h, lam_w, typ, branches, pieces, etext, h1sub):
    v1 = f'x + {e[0]}' if e[0] else 'x'
    v2 = f'y + {e[1]}' if e[1] else 'y'
    ih, lh = lam_h
    iw, lw = lam_w
    h1 = f'({v1}) - {ih} * ({AA} + 1) + 2 * {lh}'
    h2 = f'({v2}) - {ih} * ({AA} - 1) - 2 * {AA} * {lh}'
    w1 = f'({v1}) - {iw} * ({AA} + 1) + 2 * {lw}'
    w2 = f'({v2}) - {iw} * ({AA} - 1) - 2 * {AA} * {lw}'
    corner_pick = {(0, 0): 'Or.inl rfl', (1, 0): 'Or.inr (Or.inl rfl)', (0, 1): 'Or.inr (Or.inr (Or.inl rfl))',
                   (1, 1): 'Or.inr (Or.inr (Or.inr rfl))'}[tuple(e)]
    dexpr = {'H0': f'(0, -({etext}))', 'He': '(1, 0)', 'Ho': '(0, 1)', 'V0': '(1, 0)',
             'Ve': f'(({etext}), 0)', 'Vo': f'(0, -({etext}))'}[typ]
    kindH = typ in ('H0', 'He', 'Ho')
    hterm = h_hyp_term(typ, 'H' if kindH else 'V', h1sub)
    fsterm = free_site_term(typ, h1sub)
    lem = {'H0': 'freeDisp_H0 (by omega)',
           'He': f'freeDisp_Heven {hterm} (by omega) (by simp only [EvenSite]; omega)',
           'Ho': f'freeDisp_Hodd {hterm} (by omega) (by simp only [EvenSite]; omega)',
           'V0': 'freeDisp_V0 (by omega)',
           'Ve': f'freeDisp_Veven {hterm} (by omega) (by simp only [EvenSite]; omega)',
           'Vo': f'freeDisp_Vodd {hterm} (by omega) (by simp only [EvenSite]; omega)'}[typ]
    ch = charge_text(w1, w2, branches, pieces)
    return f'''  have hv : SqCorner (x, y) ({v1}, {v2}) := by
    unfold SqCorner
    exact {corner_pick}
  have hw : AliasOf (2 * (k : ℤ) + 4) ({v1}, {v2}) ({w1}, {w2}) :=
    ⟨{iw}, {lw}, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ({w1}) ({w2}) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2})) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2}))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2})) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ({w1}, {w2}))) := by
{ch}
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have hh : AliasOf (2 * (k : ℤ) + 4) ({v1}, {v2}) ({h1}, {h2}) :=
    ⟨{ih}, {lh}, by ext <;> simp⟩
  have hfs : FreeSite (2 * (k : ℤ) + 4) ({h1}) ({h2}) := {fsterm}
  have hdisp : freeDisp (2 * (k : ℤ) + 4) ({etext}) ({h1}) ({h2}) = {dexpr} := by
    exact {lem}
  have hout : SqOut (x, y) (({v1}) + ({dexpr}).1, ({v2}) + ({dexpr}).2) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_free_witness' hv hlap hh hfs hdisp hout'''


def free_site_term(typ, h1_sign):
    """an explicit proof term of FreeSite a h1 h2 for the H/V type (sub-form chosen by the first coordinate)."""
    if typ == 'H0':
        return 'Or.inl (Or.inl ⟨by omega, by omega⟩)'
    if typ in ('He',):
        return 'Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))'
    if typ in ('Ho',):
        return 'Or.inl (Or.inr (Or.inr ⟨by omega, by omega⟩))'
    if typ == 'V0' or (typ in ('Ve', 'Vo') and h1_sign == 0):
        return 'Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)'
    return 'Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)'


def h_hyp_term(typ, kind, h1_sign):
    """an explicit proof of FreeHSite (kind 'H') or FreeVSite (kind 'V') for the alias, when the type allows it."""
    if kind == 'H':
        return {'H0': '(Or.inl ⟨by omega, by omega⟩)', 'He': '(Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))',
                'Ho': '(Or.inr (Or.inr ⟨by omega, by omega⟩))'}[typ]
    return ('(Or.inl ⟨by omega, by omega, by omega⟩)' if h1_sign == 0 else '(Or.inr ⟨by omega, by omega, by omega⟩)')


def parse_free(lab):
    # lab like "F((0, 0), (1, 0), (0, -1));(1, 0);E" -> ((e, lam_h, d), lam_w, piece)
    head, lamw, piece = lab.split(';')
    e, lam_h, d = ast.literal_eval(head[1:])
    return (e, lam_h, d), ast.literal_eval(lamw), piece


def sample_data(u, K, e, sign):
    """for one sample of a free leaf: the native copy offset of the corner, its charge, and the type of the H/V alias."""
    a = 2 * K + 2
    x, y = u
    v = (x + e[0], y + e[1])
    return v


def leaf_free_text(idx, path, samples, labs):
    """samples: list of (u, K); labs: (label+, label-) strings of the leaf (both free)."""
    conds = [cond_lean(f, op, th) for f, op, th in path]
    hyps = '\n'.join(f'    (_c{j} : {c})' for j, c in enumerate(conds))
    per_sign = {}
    for sign, lab in ((1, labs[0]), (-1, labs[1])):
        (e, lam_h, d), lam_w, piece = parse_free(lab)
        types = set()
        h1s = set()
        for u, K in samples:
            a = 2 * K + 2
            x, y = u
            v = (x + e[0], y + e[1])
            h = (v[0] - lam_h[0] * (a + 1) + 2 * lam_h[1], v[1] - lam_h[0] * (a - 1) - 2 * a * lam_h[1])
            types.add(h_type(h, a))
            h1s.add(h[0] if h[0] in (0, -1) else 'H')
        if len(types) != 1 or len(h1s) != 1:
            raise ValueError('free leaf %d sign %d: H/V types %s, first coordinates %s' % (idx, sign, types, h1s))
        h1sub_sign = next(iter(h1s))
        if h1sub_sign not in (0, -1):
            h1sub_sign = 1
        if piece == 'E':
            branches, pieces = {True}, set()
        else:
            branches, pieces = {False}, {piece}
        per_sign[sign] = (e, lam_h, lam_w, next(iter(types)), d, branches, pieces, h1sub_sign)
    same = per_sign[1][:4] == per_sign[-1][:4] and per_sign[1][5] == per_sign[-1][5] and per_sign[1][6] == per_sign[-1][6] and per_sign[1][7] == per_sign[-1][7]
    head = f'''set_option maxHeartbeats 400000 in
theorem sq_leaf_{idx} (k : ℕ) {{S : Field}}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
{hyps} :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
'''
    if same:
        e, lam_h, lam_w, typ, d, br, pc, hs = per_sign[1]
        for sign in (1, -1):
            assert D_FORMULA(typ, sign) == tuple(per_sign[sign][4]), (idx, sign, typ, per_sign[sign][4])
        return head.replace('(hη : η = 1', '(_hη : η = 1') + free_block(e, lam_h, lam_w, typ, br, pc, 'η', hs) + '\n'
    parts = []
    for sign, etext in ((1, '1'), (-1, '(-1)')):
        e, lam_h, lam_w, typ, d, br, pc, hs = per_sign[sign]
        assert D_FORMULA(typ, sign) == tuple(d), (idx, sign, typ, d)
        parts.append(free_block(e, lam_h, lam_w, typ, br, pc, etext, hs))
    def bullet(block):
        lines = block.split('\n')
        out = ['  · ' + lines[0].lstrip()] + ['  ' + l for l in lines[1:]]
        return '\n'.join(out)
    return head + '  rcases hη with rfl | rfl\n' + bullet(parts[0]) + '\n' + bullet(parts[1]) + '\n'


if __name__ == '__main__':
    train = []
    for K in TRAIN_K:
        train += pair_labels(K)
    X = np.array([[f[k] for k in KEYS] for f, _, _, _ in train])
    yl = np.array([l for _, l, _, _ in train])
    clf = DecisionTreeClassifier(criterion='entropy', random_state=0).fit(X, yl)
    L = leaves(clf)
    leaf_ids = clf.apply(X)
    per_leaf = {}
    for (f, l, u, K), nid in zip(train, leaf_ids):
        per_leaf.setdefault(nid, []).append((l, u, K))
    body = ['import FLatticePaper.Plane.Induction.TwosSquares', '',
            'namespace FLatticePaper.TwosEPolicy', 'open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey',
            '']
    counts = Counter()
    for node, path, cls in L:
        entries = per_leaf.get(node, [])
        labs = set(l for l, _, _ in entries)
        if len(labs) != 1:
            raise ValueError('leaf %d not pure: %s' % (node, labs))
        lab = next(iter(labs))
        samples = [(u, K) for _, u, K in entries]
        ls = lab.split('|')
        if all(not x.startswith('F') for x in ls):
            # the non-free leaf generator of twos_square_lean.py
            from twos_square_lean import leaf_data  # noqa: E402
            nf_lab = ls[0].split(';')[0]
            branches, pieces, bands = set(), set(), set()
            for u, K in samples:
                b, p, bd = leaf_data([u], nf_lab, K)
                branches |= b
                pieces |= p
                bands |= bd
            body.append(leaf_text(node, path, nf_lab, branches, pieces, bands))
            counts['nonfree'] += 1
        else:
            body.append(leaf_free_text(node, path, samples, (ls[0], ls[1])))
            counts['free'] += 1
    body.append('end FLatticePaper.TwosEPolicy')
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'FLatticePaper', 'Plane', 'Induction',
                       'TwosSquareLeaves.lean')
    open(out, 'w').write('\n'.join(body) + '\n')
    print('leaves written', dict(counts))
