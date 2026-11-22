"""Task 43: where the constructor's standard outputs miss TeX sites, in the TeX child pieces.

Run: python3 ctor_rule.py MAXLEN

For each word w = u + d (not a pure word) and standard parity p, the TeX tile (alt_tiles.std_odd / std_even) is compared
with the constructor's output (ctor.output) in the TeX frame (the constructor's lower-left normalised tile translated by
the lowest site of the TeX tile). For each missing site x, the TeX child pieces (std_diff.pieces) containing x are
listed with the donor-local point y = x - offset, and y's position relative to the donor's lowest and upper corners
(the donor is a TeX register: stateAt(w).tOdd or .tEven). Helper slots of the constructor (replaced by the corrections):
odd phase 0: slots 1, 2; odd phase 1: slots 0, 3; even: slots 3, 4.
"""
import sys

import ctor
import alt_tiles as at
import alt_checks as ac
import std_diff as sd

HELPER = {('odd', 0): {1, 2}, ('odd', 1): {0, 3}, ('even', 0): {3, 4}, ('even', 1): {3, 4}}


def lowest(T):
    return min(T, key=lambda p: (p[1], p[0]))


def upper(T):
    return max(T, key=lambda p: (p[1], p[0]))


def missing_in_tex_frame(w, parity):
    T = frozenset(at.std_odd(w) if parity == 'odd' else at.std_even(w))
    out = ctor.output(w)
    idx = 0 if parity == 'odd' else 1
    C = out[idx]
    if not C:
        return T, frozenset(T)
    lo = lowest(T)
    Cframe = frozenset((x + lo[0], y + lo[1]) for (x, y) in ctor.llc(C))
    return T, T - Cframe


def main(argv):
    maxlen = int(argv[0])
    for w in ac.words(maxlen):
        if not w or all(c == w[0] for c in w) and w[0] != '1':
            continue
        for parity in ('odd', 'even'):
            T, M = missing_in_tex_frame(w, parity)
            if not M:
                continue
            phase = at.phase(w)
            ps = sd.pieces(w, parity)
            print('word %r %s phase %d: |T|=%d missing %d' % (w, parity, phase, len(T), len(M)))
            for x in sorted(M):
                for k, (kind, donor, off) in enumerate(ps):
                    y = (x[0] - off[0], x[1] - off[1])
                    if y in donor:
                        lo, up = lowest(donor), upper(donor)
                        helper = 'H' if k in HELPER[(parity, phase)] else '-'
                        print('   x=%s piece %d %s%s y=%s  y-low=%s upper-y=%s  [%s]' % (
                            x, k, kind, '', y, (y[0] - lo[0], y[1] - lo[1]), (up[0] - y[0], up[1] - y[1]), helper))


if __name__ == '__main__':
    main(sys.argv[1:])
