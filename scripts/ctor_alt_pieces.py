"""Task 45: the literal alternate pieces of a word, as a list (kind, donor, offset) with the alternate piece marked.

pieces_alt(word, s) mirrors alt_tiles.alt_pieces / ctor_alt_rule.pieces_with_restoration for the odd and even outputs.
Returns, for the odd and even outputs, the six standard pieces (kind 'E' or 'O', the donor tile, the offset) and the
alternate piece (kind 'aE' for the odd output, 'aO' for the even output, with its offset including the restoration).
"""
import ctor
import alt_tiles as at


def pieces_alt(word, s, r_odd, r_even):
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
    Z = (0, 0)
    if flag:
        odd = [('E', tE, V1o_p), ('E', tE, at.sub(at.add(V2_p, V2_p), V1e_q)),
               ('O', tO, Z), ('O', tO, at.add(Sp, Z)), ('O', tO, at.add(V1e_q, V2_q)), ('O', tO, at.add(at.add(V1e_q, V2_q), Sp))]
        even = [('E', tE, V1o_p), ('E', tE, at.add(V1o_p, Sq)), ('E', tE, V2_p), ('E', tE, at.add(V2_p, Sq)),
                ('O', tO, Z), ('O', tO, at.add(at.add(V2_p, V2_q), at.add(V1e_q, V1e_q)))]
    else:
        odd = [('E', tE, Z), ('E', tE, at.add(V1o_p, at.add(at.add(V2_p, V2_p), V1e_q))),
               ('O', tO, V1e_q), ('O', tO, at.add(V1e_q, Sp)), ('O', tO, V2_q), ('O', tO, at.add(V2_q, Sp))]
        even = [('E', tE, Z), ('E', tE, Sq), ('E', tE, at.add(V1o_p, V2_p)), ('E', tE, at.add(at.add(V1o_p, V2_p), Sq)),
                ('O', tO, V1e_q), ('O', tO, at.sub(at.add(V2_p, V2_q), V1e_q))]
    # the alternate pieces
    odd_alt = None
    even_alt = None
    if typ in '13':
        odd_alt = (('aE', aE, at.add(at.add(V2_p, V1o_p), at.neg(V1e_q))) if flag else ('aE', aE, at.add(V2_p, V1e_q)))
    if typ == '1':
        even_alt = ('aO', aO, at.add(V2_p, V1e_q)) if flag else ('aO', aO, at.add(at.add(V2_p, V1o_p), at.neg(V1e_q)))
    elif typ == '2':
        even_alt = ('aO', aO, at.add(at.add(V1e_q, V1e_q), V2_q)) if flag else ('aO', aO, V2_q)
    if odd_alt is not None:
        k, t, o = odd_alt
        odd_alt = (k, t, at.add(o, r_even))
    if even_alt is not None:
        k, t, o = even_alt
        even_alt = (k, t, at.add(o, r_odd))
    return odd, odd_alt, even, even_alt


def build_sets(pieces):
    out = set()
    for kind, donor, off in pieces:
        for y in donor:
            out.add((y[0] + off[0], y[1] + off[1]))
    return out
