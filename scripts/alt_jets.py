"""The jets of the ordinary alternate schedules (task 46), from Offsets.lean.

A jet is (offset, slope), each a pair of integers. kernelJet f = ((den, num), 0), transverseJet f = ((num - den, num + den),
(num, -den)) for a fraction f = (num, den). doubleFirst a b c d e = [a, a + e, b, b + e, c, d]; doubleLast a b c d e =
[a, b, c, d + e, c?]: here doubleLast a b c d e = [a, b, c, c + e, d, d + e]. The parents of a word are its odd and even Farey
parents, as parents(w) in proto2 (left = odd, right = even).
"""
from seventh_jet import kernel_jet, transverse_jet, phase, parents_of, jadd, jscale

ZERO = ((0, 0), (0, 0))


def double_first(a, b, c, d, e):
    return [a, jadd(a, e), b, jadd(b, e), c, d]


def double_last(a, b, c, d, e):
    return [a, b, c, jadd(c, e), d, jadd(d, e)]


def alternate_jets(word, parity):
    """alternateJets word parity, as a list of six jets (slot 0 to 5)."""
    word = tuple(word)
    odd_f, even_f = parents_of(word)
    oK, oT = kernel_jet(odd_f), transverse_jet(odd_f)
    eK, eT = kernel_jet(even_f), transverse_jet(even_f)
    ph = phase(word)
    neg = lambda j: jscale(-1, j)
    if parity == "odd":
        if ph == 0:
            return double_last(ZERO, jadd(jscale(2, oK), jadd(jscale(2, oT), eK)), eK, eT, jadd(eK, oT))
        return double_last(jscale(2, oK), jadd(jscale(2, oT), neg(eK)), ZERO, jadd(eK, eT), jadd(neg(eK), oT))
    if ph == 0:
        return double_first(ZERO, jadd(jscale(2, oK), oT), eK, jadd(jadd(oT, neg(eK)), eT), jadd(neg(eK), oT))
    return double_first(jscale(2, oK), oT, ZERO, jadd(jadd(oT, eT), jscale(2, eK)), jadd(eK, oT))


def seventh_offset_slope(word, parity):
    """seventhAlternateJet (beforePush, digit) parity for the word = beforePush ++ [digit]."""
    word = tuple(word)
    digit = word[-1]
    odd_f, even_f = parents_of(word)
    oK, oT = kernel_jet(odd_f), transverse_jet(odd_f)
    eK, eT = kernel_jet(even_f), transverse_jet(even_f)
    ph = phase(word)
    if parity == "odd":
        if ph == 0:
            return jadd(eK, oT)
        if digit == 2:
            return oT
        return jadd(oT, jadd(jscale(2, oK), jscale(-1, eK)))
    if ph == 0:
        if digit == 1:
            return jadd(oT, jadd(jscale(2, oK), jscale(-1, eK)))
        return eT
    if digit == 2:
        return jadd(jscale(2, eK), eT)
    return jadd(eK, oT)


def lexmin(sites):
    """The lowest row, then the leftmost site of that row (rowKey: (y, x) lexicographic)."""
    return min(sites, key=lambda s: (s[1], s[0]))


if __name__ == "__main__":
    for w in [(1,), (2,), (1, 1), (1, 3)]:
        print(w, "even slots offsets", [j[0] for j in alternate_jets(w, "even")], "seventh", seventh_offset_slope(w, "even")[0])
