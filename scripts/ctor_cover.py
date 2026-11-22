"""Task 43, part 3 numerics: deck coverage of the constructor's standard tiles (the Python port, ctor.py), for all words of
length <= MAXLEN.

Run: python3 ctor_cover.py MAXLEN

For a word w and parity p, f = current(parents_at(w), p) and the modified deck of f (deck_cover.deck_basis). The
constructor's register covers the deck iff its sites meet every class of Z^2 modulo the deck lattice (deck_cover.covers).
Since the TeX tile covers the deck, this is equivalent to: each site removed from the TeX tile is congruent modulo the
deck to a site that stays (the hypothesis of covers_of_removed in DeckCoverage.lean).
"""
import sys

import ctor
import alt_tiles as at
import alt_checks as ac
import deck_cover as dc


def main(argv):
    maxlen = int(argv[0])
    total = 0
    not_cover = []
    tex_not = []
    for w in ac.words(maxlen):
        P = at.parents_at(w)
        out = ctor.output(w)
        for parity in ('odd', 'even'):
            f = at.current(P, parity)
            basis = dc.deck_basis(f, parity == 'odd')
            T = frozenset(at.std_odd(w) if parity == 'odd' else at.std_even(w))
            ok_t, _, _ = dc.covers(T, basis)
            C = out[0 if parity == 'odd' else 1]
            ok_c, _, _ = dc.covers(C, basis)
            total += 1
            if not ok_t:
                tex_not.append((w, parity))
            if not ok_c:
                not_cover.append((w, parity))
    print('words of length <= %d: %d; standard registers checked: %d' % (maxlen, len(ac.words(maxlen)), total))
    print('TeX standard tiles not covering their deck: %d %s' % (len(tex_not), tex_not[:5]))
    print('constructor standard tiles not covering their deck: %d %s' % (len(not_cover), not_cover[:5]))


if __name__ == '__main__':
    main(sys.argv[1:])
