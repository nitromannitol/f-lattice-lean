"""Task 45: the joint rule for the constructor's alternate outputs, as a recursion, tested against the port.

Run: python3 ctor_alt_predict.py MAXLEN

TA(w, p): the literal alternate tile of the output of w (parity p) with the head restorations, computed from the TeX
standard tiles of the parents (at.std_state, normalised) and the TeX alternate retained tiles (the outputs at the birth
words): the six standard pieces and the alternate piece of ctor_alt_pieces.pieces_alt, normalised to the lowest site.

Predicted missing set DA(w, p) (in the normalised frame of TA(w, p)): a site x of TA is missing iff every piece containing
x misses it, where a piece misses
  * for a standard piece with donor kind K (E or O) at the donor label of w (ctor_predict.donor_label): the missing set
    of the standard register of that label (ctor_predict.D), in its donor frame;
  * for the alternate piece (aE for the odd output, aO for the even output): the missing set DA of the alternate register
    of the donor label (same label as the standard donor of that kind), in its frame;
  * for the even output after digit 3 with a pure-2 ancestor (the own pair): piece 0 misses (2, 0) and piece 3 misses
    (up - 2, 0) where up is the upper site of its donor (the E donor of that piece).
Compared with the port: ctor.output(w) (the alternate components), normalised.
"""
import sys
from functools import lru_cache

import ctor
import alt_tiles as at
import alt_checks as ac
import ctor_predict as cp
import ctor_alt_pieces as cap
from ctor_alt_rule import norm, pieces_with_restoration

ZERO_N = norm(at.ZERO)
ONE_N = norm(at.ONE)


def lowest(T):
    return min(T, key=lambda p: (p[1], p[0]))


def upper(T):
    return max(T, key=lambda p: (p[1], p[0]))


def is_base(w):
    return w == '' or at.is_all(w, '2') or at.is_all(w, '3')


@lru_cache(maxsize=None)
def std_after(w):
    par, tO, tE = at.std_state(w)
    return par, norm(tO), norm(tE)


@lru_cache(maxsize=None)
def retained_alt(w):
    """(aO, aE) of the alternate retained registers after w (normalised)."""
    if w == '':
        return ZERO_N, ONE_N
    pre, d = w[:-1], w[-1]
    aO, aE = retained_alt(pre)
    odd_pre, even_pre = alt_out(pre)
    if d == '1':
        return odd_pre, even_pre
    if d == '2':
        return odd_pre, aE
    return aO, even_pre


@lru_cache(maxsize=None)
def alt_out(w):
    """(TA odd, TA even) of the output of w, normalised."""
    if is_base(w):
        a1, a2 = at.alt_base(w)
        return norm(a1), norm(a2)
    par, tO, tE = std_after(w)
    aO, aE = retained_alt(w)
    s = (par, tO, tE, aO, aE)
    r_even = ctor.alternateRestorationOff(w, 'even')
    r_odd = ctor.alternateRestorationOff(w, 'odd')
    Lo, Le = pieces_with_restoration(w, s, r_odd, r_even)
    return norm(Lo), norm(Le)


def pieces_of(w):
    """Pieces (kind, donor, offset, label kind) and the alternate piece of the two outputs, from TeX normalised donors."""
    par, tO, tE = std_after(w)
    aO, aE = retained_alt(w)
    s = (par, tO, tE, aO, aE)
    r_even = ctor.alternateRestorationOff(w, 'even')
    r_odd = ctor.alternateRestorationOff(w, 'odd')
    odd, oa, even, ea = cap.pieces_alt(w, s, r_odd, r_even)
    return odd, oa, even, ea


@lru_cache(maxsize=None)
def DA(w, parity):
    """Predicted missing sites of the alternate output of w (parity), in the normalised frame of alt_out(w)[idx]."""
    if is_base(w):
        return frozenset()
    odd_pc, oa, even_pc, ea = pieces_of(w)
    if parity == 'odd':
        if w[-1] not in '13':
            pcs, alt = odd_pc, None
        else:
            pcs, alt = odd_pc, oa
    else:
        if w[-1] not in '12':
            pcs, alt = even_pc, None
        else:
            pcs, alt = even_pc, ea
    own = parity == 'even' and w[-1] == '3' and ctor_ancestor_pure2(w)
    # the sets of the pieces (absolute frame) and each piece's missing set
    miss_list = []
    for k, (kind, donor, off) in enumerate(pcs):
        if own and k in (0, 3):
            up = upper(donor)
            miss = {(2, 0)} if k == 0 else {(up[0] - 2, up[1])}
            miss_list.append((donor, off, frozenset(miss)))
        else:
            lab = donor_label2(w, kind)
            miss_list.append((donor, off, missing_std(lab, kind, donor)))
    if alt is not None:
        kind_alt, t_alt, off_alt = alt
        lab = donor_label2(w, 'E' if parity == 'odd' else 'O')
        miss_list.append((t_alt, off_alt, missing_alt(lab, 'even' if parity == 'odd' else 'odd')))
    # absolute set and the rule
    cover = set()
    for donor, off, _ in miss_list:
        for y in donor:
            cover.add((y[0] + off[0], y[1] + off[1]))
    out = set()
    for x in cover:
        containing = []
        ok = True
        for donor, off, miss in miss_list:
            y = (x[0] - off[0], x[1] - off[1])
            if y in donor:
                containing.append(y)
                if y not in miss:
                    ok = False
                    break
        if ok and containing:
            out.add(x)
    lo = lowest(frozenset(cover))
    return frozenset((x[0] - lo[0], x[1] - lo[1]) for x in out)


def donor_label2(w, kind):
    """The label of a standard donor of kind 'E' (even) or 'O' (odd) of the step w (ctor_predict.donor_label)."""
    kind2 = 'even' if kind == 'E' else 'odd'
    return cp.donor_label(w, kind2, kind2)


def missing_std(lab, kind, donor):
    if lab is None:
        return frozenset()
    dk = 'even' if kind == 'E' else 'odd'
    return frozenset(cp.D(lab, dk))


def missing_alt(lab, parity):
    if lab is None:
        return frozenset()
    return DA(lab, parity)


def ctor_ancestor_pure2(w):
    u = w[:-1]
    st = ctor.evaluate(u)
    anc = st['savedThree'][0]
    return bool(anc) and all(c == '2' for c in anc)


def main(argv):
    maxlen = int(argv[0])
    total = 0
    bad = []
    for w in ac.words(maxlen):
        if is_base(w):
            continue
        st = ctor.evaluate(w)
        regs = st['cur'][1]
        for parity, idx, name in (('odd', 0, 'co'), ('even', 1, 'ce')):
            total += 1
            TA = alt_out(w)[idx]
            C = norm(ctor.llc(regs['al'][name])) if regs['al'][name] else frozenset()
            actual_missing = frozenset(TA - C)
            actual_extra = frozenset(C - TA)
            pred = DA(w, parity)
            if actual_missing != pred or actual_extra:
                bad.append((w, parity, sorted(actual_missing - pred)[:3], sorted(pred - actual_missing)[:3],
                            sorted(actual_extra)[:3]))
    print('alternate outputs predicted: %d; mismatches: %d' % (total, len(bad)))
    for b in bad[:30]:
        print('  ', b)


if __name__ == '__main__':
    main(sys.argv[1:])
