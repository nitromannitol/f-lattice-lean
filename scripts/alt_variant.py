"""Task 33 experiment: the seventh-piece placements of the constructor (Construction/Offsets.lean seventhAlternateJet)
versus the TeX (omitted pieces '-'). Used only to compare readings; alt_tiles.py holds the TeX reading."""
import alt_tiles as at
from alt_tiles import shift, add, neg, V1o, V1e, V2, phase


def sub2(u, v):
    return (u[0] - v[0], u[1] - v[1])


def pieces_with(seventh_rule):
    def pieces(word, s):
        par, tO, tE, aO, aE = s
        p1, q1 = par
        flag = phase(word) == 1
        typ = word[-1]
        V1o_p, V2_p, V1e_q, V2_q = V1o(p1), V2(p1), V1e(q1), V2(q1)
        if flag:
            Sp = add(neg(V1e_q), V2_p); Sq = add(V1e_q, V2_p)
        else:
            Sp = add(V1e_q, V2_p); Sq = add(neg(V1e_q), V2_p)

        def dsP(o):
            return shift(tO, o) | shift(tO, add(o, Sp))

        def dsQ(o):
            return shift(tE, o) | shift(tE, add(o, Sq))

        Z = (0, 0)
        if flag:
            odd = (shift(tE, V1o_p) | shift(tE, sub2(add(V2_p, V2_p), V1e_q)) | dsP(Z) | dsP(add(V1e_q, V2_q)))
            even = (dsQ(V1o_p) | dsQ(V2_p) | shift(tO, Z) | shift(tO, add(add(V2_p, V2_q), add(V1e_q, V1e_q))))
        else:
            odd = (shift(tE, Z) | shift(tE, add(V1o_p, add(add(V2_p, V2_p), V1e_q))) | dsP(V1e_q) | dsP(V2_q))
            even = (dsQ(Z) | dsQ(add(V1o_p, V2_p)) | shift(tO, V1e_q) | shift(tO, sub2(add(V2_p, V2_q), V1e_q)))
        o_alt, e_alt = seventh_rule(typ, flag, V1o_p, V2_p, V1e_q, V2_q)
        if o_alt is not None:
            odd = odd | shift(aE, o_alt)
        if e_alt is not None:
            even = even | shift(aO, e_alt)
        return odd, even
    return pieces


def tex_rule(typ, flag, V1o_p, V2_p, V1e_q, V2_q):
    if flag:   # odd-first
        o = add(add(V2_p, V1o_p), neg(V1e_q)) if typ in '13' else None
        e = {'1': add(V2_p, V1e_q), '2': add(add(V1e_q, V1e_q), V2_q)}.get(typ)
    else:      # even-first
        o = add(V1e_q, V2_p) if typ in '13' else None
        e = {'1': add(add(V2_p, V1o_p), neg(V1e_q)), '2': V2_q}.get(typ)
    return o, e


def constructor_rule(typ, flag, V1o_p, V2_p, V1e_q, V2_q):
    # Offsets.lean seventhAlternateJet: .odd, true (even-first) -> K_e + T_o for every digit;
    # .odd, false (odd-first): digit 2 -> T_o, digit 1,3 -> T_o + 2K_o - K_e;
    # .even, true (even-first): digit 1 -> T_o + 2K_o - K_e, 2 -> T_e, 3 -> T_o + K_e - 2(K_e - 2K_o);
    # .even, false (odd-first): digit 2 -> 2K_e + T_e, 1,3 -> K_e + T_o.
    if not flag:  # even-first (phase word = 0)
        o = add(V1e_q, V2_p)
        e = {'1': add(V2_p, V1o_p) if False else add(add(V2_p, V1o_p), neg(V1e_q)),
             '2': V2_q,
             '3': add(sub2(V2_p, V1e_q), add(V1o_p, V1o_p))}.get(typ)
        return o, e
    o = V2_p if typ == '2' else add(add(V2_p, V1o_p), neg(V1e_q))
    e = add(add(V1e_q, V1e_q), V2_q) if typ == '2' else add(V1e_q, V2_p)
    return o, e


def rule_summary():
    pass
