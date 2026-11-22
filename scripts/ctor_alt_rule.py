"""Task 45: the constructor's ordinary alternate outputs against the literal alternate pieces, with the head restoration.

Run: python3 ctor_alt_rule.py MAXLEN

For a word w and its registers after w (ctor.evaluate), the literal alternate pieces alt_tiles.alt_pieces(w, s) are
computed from s = (parents of w, the standard retained registers after w, the alternate retained registers after w);
the piece that uses the alternate retained even (odd output) is shifted by the head restoration r = alternateRestoration
(w, even), and the piece that uses the alternate retained odd (even output) by r = alternateRestoration(w, odd).
Ordinary outputs: the odd alternate of a word ending in 1 or 3, the even alternate of a word ending in 1 or 2.
"""
import sys

import ctor
import alt_tiles as at
import alt_checks as ac


def norm(T):
    T = frozenset(T)
    if not T:
        return T
    lo = min(T, key=lambda p: (p[1], p[0]))
    return frozenset((x - lo[0], y - lo[1]) for (x, y) in T)


def pieces_with_restoration(word, s, r_odd, r_even):
    """alt_tiles.alt_pieces with the alternate even piece of the odd child shifted by r_even and the alternate odd piece of
    the even child shifted by r_odd (the head restorations)."""
    par, tO, tE, aO, aE = s
    p1, q1 = par
    flag = at.phase(word) == 1
    typ = word[-1]
    V1o_p, V2_p, V1e_q, V2_q = at.V1o(p1), at.V2(p1), at.V1e(q1), at.V2(q1)
    if flag:
        Sp = at.add(at.neg(V1e_q), V2_p)
        Sq = at.add(V1e_q, V2_p)
    else:
        Sp = at.add(V1e_q, V2_p)
        Sq = at.add(at.neg(V1e_q), V2_p)

    def dsP(o):
        return at.shift(tO, o) | at.shift(tO, at.add(o, Sp))

    def dsQ(o):
        return at.shift(tE, o) | at.shift(tE, at.add(o, Sq))

    Z = (0, 0)
    if flag:
        odd = (at.shift(tE, V1o_p) | at.shift(tE, at.sub(at.add(V2_p, V2_p), V1e_q))
               | dsP(Z) | dsP(at.add(V1e_q, V2_q)))
        odd_alt = at.add(at.add(V2_p, V1o_p), at.neg(V1e_q)) if typ in '13' else None
        even = (dsQ(V1o_p) | dsQ(V2_p) | at.shift(tO, Z) | at.shift(tO, at.add(at.add(V2_p, V2_q), at.add(V1e_q, V1e_q))))
        even_alt = at.add(V2_p, V1e_q) if typ == '1' else (at.add(at.add(V1e_q, V1e_q), V2_q) if typ == '2' else None)
    else:
        odd = (at.shift(tE, Z) | at.shift(tE, at.add(V1o_p, at.add(at.add(V2_p, V2_p), V1e_q)))
               | dsP(V1e_q) | dsP(V2_q))
        odd_alt = at.add(V2_p, V1e_q) if typ in '13' else None
        even = (dsQ(Z) | dsQ(at.add(V1o_p, V2_p)) | at.shift(tO, V1e_q) | at.shift(tO, at.sub(at.add(V2_p, V2_q), V1e_q)))
        even_alt = at.add(at.add(V2_p, V1o_p), at.neg(V1e_q)) if typ == '1' else (V2_q if typ == '2' else None)
    if odd_alt is not None:
        odd = odd | at.shift(aE, at.add(odd_alt, r_even))
    if even_alt is not None:
        even = even | at.shift(aO, at.add(even_alt, r_odd))
    return odd, even


def main(argv):
    maxlen = int(argv[0])
    words = [w for w in ac.words(maxlen) if w and not at.is_all(w, '2') and not at.is_all(w, '3')]
    res = {}
    bad = {'odd': [], 'even': []}
    for w in words:
        st = ctor.evaluate(w)
        regs = st['cur'][1]
        par = at.parents_at(w)
        tO = regs['st']['ro']
        tE = regs['st']['re']
        aO = regs['al']['ro']
        aE = regs['al']['re']
        s = (par, tO, tE, aO, aE)
        r_even = ctor.alternateRestorationOff(w, 'even')
        r_odd = ctor.alternateRestorationOff(w, 'odd')
        for label, digit_ok, idx, ctor_name in (('odd', w[-1] in '13', 0, 'co'), ('even', w[-1] in '12', 1, 'ce')):
            if not digit_ok:
                continue
            Lo, Le = pieces_with_restoration(w, s, r_odd, r_even)
            L = Lo if label == 'odd' else Le
            C = regs['al'][ctor_name]
            res.setdefault(label, 0)
            res[label] += 1
            if norm(L) != norm(ctor.llc(C)):
                bad[label].append(w)
    print('ordinary alternate outputs checked:', res)
    print('mismatches (odd):', len(bad['odd']), bad['odd'][:20])
    print('mismatches (even):', len(bad['even']), bad['even'][:20])


if __name__ == '__main__':
    main(sys.argv[1:])
