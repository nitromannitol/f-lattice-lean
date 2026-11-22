"""Task 45: where the corrected alternate even outputs (digit 3) miss the literal pieces, in the pieces' donor frames.

Run: python3 ctor_alt_own.py MAXLEN

For each word w ending in 3 (not pure), the literal alternate even set (with the restorations) is compared with the
constructor's output in the literal frame. Each missing site is located in the literal pieces (kind, donor, offset) and
the donor-local point is given with its position relative to the donor's lowest and upper site.
"""
import sys

import ctor
import alt_tiles as at
import alt_checks as ac
import ctor_alt_pieces as cap
from ctor_alt_rule import norm


def lowest(T):
    return min(T, key=lambda p: (p[1], p[0]))


def upper(T):
    return max(T, key=lambda p: (p[1], p[0]))


def main(argv):
    maxlen = int(argv[0])
    for w in ac.words(maxlen):
        if not w or at.is_all(w, '2') or at.is_all(w, '3') or w[-1] != '3':
            continue
        st = ctor.evaluate(w)
        regs = st['cur'][1]
        s = (at.parents_at(w), regs['st']['ro'], regs['st']['re'], regs['al']['ro'], regs['al']['re'])
        r_even = ctor.alternateRestorationOff(w, 'even')
        r_odd = ctor.alternateRestorationOff(w, 'odd')
        odd, oa, even, ea = cap.pieces_alt(w, s, r_odd, r_even)
        pcs = even + ([ea] if ea else [])
        Labs = cap.build_sets(pcs)
        lo = lowest(Labs)
        C = ctor.llc(regs['al']['ce'])
        Cabs = frozenset((x + lo[0], y + lo[1]) for (x, y) in C)
        miss = sorted(Labs - Cabs)
        extra = sorted(Cabs - Labs)
        if not miss and not extra:
            print('%-6r even: equal to the literal pieces' % w)
            continue
        print('%-6r even: missing %d extra %d' % (w, len(miss), len(extra)))
        for x in miss:
            for k, (kind, donor, off) in enumerate(pcs):
                y = (x[0] - off[0], x[1] - off[1])
                if y in donor:
                    l, u = lowest(donor), upper(donor)
                    print('    x=%s piece %d %s y=%s y-low=%s upper-y=%s' % (
                        x, k, kind, y, (y[0] - l[0], y[1] - l[1]), (u[0] - y[0], u[1] - y[1])))
        if extra:
            print('    extra', extra[:4])


if __name__ == '__main__':
    main(sys.argv[1:])
