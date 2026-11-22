"""Seventh copy of the ordinary even alternate (task 46, Lean jets in Python).

Jets follow Offsets.lean: kernelJet f = ((den, num), 0), transverseJet f = ((num - den, num + den), (num, -den)); a jet is
(offset, slope), a placement sends height h to h(x - offset) + slope . x. The parents of a word are its left (odd) and right
(even) Farey parents, as parents(w) in proto2.py. The seventh jet of the even alternate (seventhAlternateJet, parity even)
is computed for the word w = beforePush ++ [digit]; the restoration alternateRestoration has zero slope.
"""
import sys


def vadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def vscale(k, a):
    return (k * a[0], k * a[1])


def jadd(j, k):
    return (vadd(j[0], k[0]), vadd(j[1], k[1]))


def jscale(n, j):
    return (vscale(n, j[0]), vscale(n, j[1]))


def kernel_jet(f):
    num, den = f
    return ((den, num), (0, 0))


def transverse_jet(f):
    num, den = f
    return ((num - den, num + den), (num, -den))


def phase(w):
    return sum(1 for d in w if d == 1) % 2


def parents_of(w):
    """(odd, even) Farey parents of w as (num, den) pairs, from proto2.parents (left, right)."""
    import ordinary_tile_check as otc
    global _NS
    if "_NS" not in globals():
        _NS = otc.load_proto()
    (N, D), (nq, dq) = _NS["parents"](list(w))
    return (N, D), (nq, dq)


def seventh_jet(w):
    """seventhAlternateJet of w = beforePush ++ [digit] at parity even (digit is the last letter of w)."""
    w = tuple(w)
    digit = w[-1]
    odd_f, even_f = parents_of(w)
    oddK, oddT = kernel_jet(odd_f), transverse_jet(odd_f)
    evenK, evenT = kernel_jet(even_f), transverse_jet(even_f)
    if phase(w) == 0:
        if digit == 1:
            return jadd(oddT, jadd(jscale(2, oddK), jscale(-1, evenK)))
        return evenT
    if digit == 2:
        return jadd(jscale(2, evenK), evenT)
    return jadd(evenK, oddT)


if __name__ == "__main__":
    for w in [(1,), (2,), (1, 1), (1, 2), (2, 1), (3, 1), (1, 1, 1)]:
        print(w, "seventh jet", seventh_jet(w))
