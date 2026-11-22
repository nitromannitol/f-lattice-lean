"""Task 43: the rule for the constructor's missing standard sites, tested as a recursion (ctor.py is the port).

Run: python3 ctor_predict.py MAXLEN [VARIANT]     (default VARIANT 'inh', the rule below)

For a standard parity p and a non-pure word w, the TeX tile TeX(w, p) is the union of six pieces (std_diff.pieces): each
piece k has a donor kind E or O and an offset off_k. The constructor's register C(w, p) misses D(w, p) = TeX(w, p) minus
C(w, p), and the rule predicts D as follows. Piece k misses a set M_k in its donor's frame:
  * the donor is the TeX register of the donor kind at the donor label (donor_label): the current register of the prefix
    u = w[:-1] or the retained register, labelled by its birth word (retainedBirth). Its missing set is D(label, kind),
    by recursion. Pure words have D = empty (the base runs are exact).
  * for a corrected output (odd with last digit 3, even with last digit 2) and a helper slot (odd phase 0: slots 1, 2;
    odd phase 1: slots 0, 3; even: slots 3, 4), M_k is the donor's own missing set, except for an odd phase-0 output whose
    saved ancestor is a pure run of twos: slot 1 misses (2, 0) and slot 2 misses (up - 2, 0) in the donor frame, where up is
    the upper-right site of the donor (the own pair).
A site x of TeX(w, p) is missing iff every piece containing x misses x (x - off_k in M_k for each such piece k).
Scope of the checks: words of length <= 4 (224 registers, zero mismatches for 'inh'; length 5, 706 registers, zero
mismatches). Variant 'pair' omits the inheritance of helper slots (they miss nothing): it fails on 2313 odd and 2323 odd
(length 4). Variant 'none' omits the own pair too: it fails on 23 odd.
"""
import sys
from functools import lru_cache

import ctor
import alt_tiles as at
import alt_checks as ac
import std_diff as sd

HELPER = {('odd', 0): {1, 2}, ('odd', 1): {0, 3}, ('even', 0): {3, 4}, ('even', 1): {3, 4}}
VARIANT = 'inh'


def lowest(T):
    return min(T, key=lambda p: (p[1], p[0]))


def upper(T):
    return max(T, key=lambda p: (p[1], p[0]))


def donor_label(w, slot_parity, kind):
    """The word whose output register is the donor at the piece: current registers are labelled by the prefix u, retained
    registers by the birth word (retainedBirth). Returns None for the endpoint (empty retained, base)."""
    u, d = w[:-1], w[-1]
    if kind == 'odd':
        if d == '3':
            return ctor.retainedBirth(u, 'odd') if u else None
        return u
    if d == '2':
        return ctor.retainedBirth(u, 'even') if u else None
    return u


def saved_ancestor(w):
    """The word of the register saved for the correction of the last step of w (savedThree for an odd output, savedTwo
    for an even output), read from the constructor's state before the last digit."""
    u = w[:-1]
    st = ctor.evaluate(u)
    return st['savedThree'][0] if w[-1] == '3' else st['savedTwo'][0]


def pure(w):
    return bool(w) and all(c == w[0] for c in w) and w[0] != '1'


@lru_cache(maxsize=None)
def D(w, parity):
    """Predicted missing sites of the TeX register of `parity` at word w, in the TeX frame (normalised, low = origin)."""
    if w == '' or pure(w):
        return frozenset()
    T = frozenset(at.std_odd(w) if parity == 'odd' else at.std_even(w))
    ps = sd.pieces(w, parity)
    phase = at.phase(w)
    miss_k = []
    corrected = (parity == 'odd' and w[-1] == '3') or (parity == 'even' and w[-1] == '2')
    for k, (kind, donor, off) in enumerate(ps):
        if corrected and k in HELPER[(parity, phase)]:
            miss = set()
            ancestor = saved_ancestor(w)
            pure_anc = bool(ancestor) and all(c == '2' for c in ancestor)
            if VARIANT in ('pair', 'inh') and parity == 'odd' and phase == 0 and pure_anc:
                up = upper(donor)
                if k == 1:
                    miss = {(2, 0)}
                elif k == 2:
                    miss = {(up[0] - 2, up[1])}
            elif VARIANT == 'inh':
                # no own pair: the helper misses what its donor misses
                dk = 'odd' if kind == 'O' else 'even'
                lab = donor_label(w, parity, dk)
                miss = set(D(lab, dk)) if lab is not None else set()
            miss_k.append(frozenset(miss))
        else:
            dk = 'odd' if kind == 'O' else 'even'
            lab = donor_label(w, parity, dk)
            if lab is None:
                miss_k.append(frozenset())
            else:
                miss_k.append(D(lab, dk))
    out = set()
    for x in T:
        cover = [k for k, (kind, donor, off) in enumerate(ps) if (x[0] - off[0], x[1] - off[1]) in donor]
        if cover and all((x[0] - ps[k][2][0], x[1] - ps[k][2][1]) in miss_k[k] for k in cover):
            out.add(x)
    return frozenset(out)


def main(argv):
    global VARIANT
    maxlen = int(argv[0])
    if len(argv) > 1:
        VARIANT = argv[1]
    bad = []
    total = 0
    for w in ac.words(maxlen):
        if not w or pure(w):
            continue
        for parity in ('odd', 'even'):
            total += 1
            T = frozenset(at.std_odd(w) if parity == 'odd' else at.std_even(w))
            out = ctor.output(w)[0 if parity == 'odd' else 1]
            lo = lowest(T)
            Cf = frozenset((x + lo[0], y + lo[1]) for (x, y) in ctor.llc(out)) if out else frozenset()
            actual = T - Cf
            pred = D(w, parity)
            if actual != pred:
                bad.append((w, parity, sorted(actual - pred), sorted(pred - actual)))
    print('variant %s: %d register predictions; mismatches %d' % (VARIANT, total, len(bad)))
    for (w, p, extra, lacking) in bad[:40]:
        print('  %-6r %-4s actual-only %s predicted-only %s' % (w, p, extra[:4], lacking[:4]))


if __name__ == '__main__':
    main(sys.argv[1:])
