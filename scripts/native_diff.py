"""Task 34: where the literal and the constructor readings differ on the claims of lemma:alternate_tile_properties.

Usage: python3 native_diff.py LOG [LOG ...]   (the logs are the output of checks/NativeTiles.lean and checks/NativeTilesRoots.lean)
For every claim, the failing child tiles of each reading are compared as sets of (word, name):
  only literal  : the literal reading fails, the constructor passes;
  only constructor: the constructor fails, the literal passes;
  both          : both fail.
"""
import sys

import alt_tiles as at
import native_compare as nc
import alt_checks as ac


def main(paths):
    tiles, errors = nc.parse_all(paths)
    words = sorted({w for (w, _) in tiles}, key=lambda s: (len(s), s))
    words = [w for w in words if w]
    # the words beginning with 2 or 3 from the BFS run are E lines; use only the tiles present
    lit = nc.claims_for(
        lambda w, name: nc.normalised(at.alt_odd(w) if name == 'altOdd' else at.alt_even(w)) if w else None, words)
    con = nc.claims_for(lambda w, name: tiles.get((w, name)), words)
    claims = sorted(set(lit) | set(con))
    for k in claims:
        a = set(lit.get(k, []))
        b = set(con.get(k, []))
        only_l = sorted(a - b, key=lambda t: (len(t[0]), t[0], t[1]))
        only_c = sorted(b - a, key=lambda t: (len(t[0]), t[0], t[1]))
        both = sorted(a & b, key=lambda t: (len(t[0]), t[0], t[1]))
        print('%s: literal %d, constructor %d, both %d' % (k, len(a), len(b), len(both)))
        print('   literal only (constructor passes): %d, first %s' % (len(only_l), only_l[:6]))
        print('   constructor only (literal passes): %d, first %s' % (len(only_c), only_c[:6]))


if __name__ == '__main__':
    main(sys.argv[1:])
