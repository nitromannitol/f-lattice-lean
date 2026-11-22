"""Task 34: the constructor's output tiles (checks/NativeTiles.lean, printed by #eval) against the literal readings.

Usage: python3 native_compare.py LOGFILE
The log holds lines `T <word> <tile> <x,y;...>` and `E <word> <error>`.
Comparisons (all up to translation, after moving the lowest cell to the origin):
  C1 standard odd/even: constructor vs StandardTiles (alt_tiles.std_odd / std_even);
  C2 alternate odd/even: constructor vs the literal TeX reading (alt_tiles.alt_odd / alt_even);
  C3 claims of lemma:alternate_tile_properties on the constructor's alternate tiles: holes, 180-degree symmetry, row
     convexity, edge connectedness, rotation identity with tF, covering of the lattice vertices under L'.
"""
import sys
from collections import defaultdict

import alt_tiles as at
import alt_checks as ac


def parse(path):
    tiles = {}
    errors = {}
    with open(path) as fh:
        for line in fh:
            line = line.rstrip('\n')
            if line.startswith('T '):
                parts = line.split(' ', 3)
                word, name = parts[1], parts[2]
                cells = parts[3] if len(parts) > 3 else ''
                pts = set()
                if cells:
                    for c in cells.split(';'):
                        x, y = c.split(',')
                        pts.add((int(x), int(y)))
                tiles[(word, name)] = frozenset(pts)
            elif line.startswith('E '):
                parts = line.split(' ', 2)
                errors[parts[1]] = parts[2] if len(parts) > 2 else ''
    return tiles, errors


def word_of(s):
    return s  # words are strings over '1','2','3'; the empty word is ''


def lower_left(T):
    return min(T, key=lambda p: (p[1], p[0]))


def normalised(T):
    if not T:
        return T
    return at.shift(T, at.neg(lower_left(T)))


def parse_all(paths):
    tiles, errors = {}, {}
    for path in paths:
        t, e = parse(path)
        for k, v in t.items():
            if k in tiles and tiles[k] != v:
                raise SystemExit('conflicting tiles for %s' % (k,))
            tiles[k] = v
        errors.update(e)
    return tiles, errors


def main(argv):
    tiles, errors = parse_all(argv)
    words = sorted({w for (w, _) in tiles} | set(errors), key=lambda s: (len(s), s))
    print('words in log: %d, evaluator errors: %d' % (len(words), len(errors)))
    for w, e in sorted(errors.items())[:10]:
        print('  error at', repr(w), e[:120])
    # C0: is llCenter's origin the lowest cell of the constructor's tiles?
    not_origin = []
    for (w, name), T in tiles.items():
        if T and lower_left(T) != (0, 0):
            not_origin.append((w, name, lower_left(T)))
    print('constructor tiles whose lowest cell is not the origin: %d' % len(not_origin))
    if not_origin:
        print('  smallest:', min(not_origin, key=lambda t: (len(t[0]), t[0])))
    # C1: standard
    std_bad = []
    for w in words:
        for name, lit in (('stdOdd', at.std_odd(w)), ('stdEven', at.std_even(w))):
            if (w, name) not in tiles:
                continue
            c = tiles[(w, name)]
            if normalised(c) != normalised(lit):
                std_bad.append((w, name))
    print('C1 standard tiles differing from StandardTiles (up to translation): %d of %d' %
          (len(std_bad), 2 * len([w for w in words if (w, 'stdOdd') in tiles])))
    if std_bad:
        print('  smallest:', min(std_bad, key=lambda t: (len(t[0]), t[0])))
    # C2: alternate vs literal reading
    alt_bad = []
    for w in words:
        for name, lit in (('altOdd', at.alt_odd(w) if w else None), ('altEven', at.alt_even(w) if w else None)):
            if (w, name) not in tiles or lit is None:
                continue
            if normalised(tiles[(w, name)]) != normalised(lit):
                alt_bad.append((w, name))
    print('C2 alternate tiles differing from the literal TeX reading (up to translation): %d' % len(alt_bad))
    if alt_bad:
        print('  smallest:', min(alt_bad, key=lambda t: (len(t[0]), t[0])))
    claims_side_by_side(tiles, words)
    return tiles, words


def claims_for(getter, words):
    """The claims of lemma:alternate_tile_properties on the alternate child tiles given by getter(word, name)."""
    res = defaultdict(list)
    for w in words:
        if not w or at.is_all(w, '2') or at.is_all(w, '3'):
            continue
        P = at.parents_at(w)
        sw = at.swapW(w)
        for name in ('altOdd', 'altEven'):
            T = getter(w, name)
            if T is None:
                continue
            if not ac.row_convex(T)[0]:
                res['row-convex'].append((w, name))
            if not ac.edge_connected(T):
                res['edge-connected'].append((w, name))
            if not ac.hole_free(T):
                res['hole-free'].append((w, name))
            if not ac.point_symmetric(T)[0]:
                res['180-symmetric'].append((w, name))
            if at.lowest(T) != (0, 0):
                res['lowest cell at origin'].append((w, name))
            unc, _ = ac.vertex_coverage(T, at.current(P, 'odd' if name == 'altOdd' else 'even'))
            if unc:
                res['covering under L′'].append((w, name))
        # rotation identity: R(T̂(p0)) = T̂(q0 of swapW w) + tF(current), and the even analogue
        for name, other, parity in (('altOdd', 'altEven', 'odd'), ('altEven', 'altOdd', 'even')):
            T = getter(w, name)
            Tp = getter(sw, other)
            if T is None or Tp is None:
                continue
            tw = at.tF(at.current(P, parity))
            if at.shift(Tp, tw) == at.rot(T):
                continue
            if ac.translation_between(Tp, at.rot(T)) is None:
                res['rotation identity (shape)'].append((w, name))
            else:
                res['rotation identity (translation only)'].append((w, name))
    return res


def smallest(items):
    return min(items, key=lambda t: (len(t[0]), t[0])) if items else None


def claims_side_by_side(tiles, words):
    # both sides normalised to their lowest cell at the origin, as llCenter does for the constructor
    lit = claims_for(lambda w, name: normalised(at.alt_odd(w) if name == 'altOdd' else at.alt_even(w)) if w else None,
                     words)
    con = claims_for(lambda w, name: tiles.get((w, 'altOdd' if name == 'altOdd' else 'altEven')), words)
    keys = sorted(set(lit) | set(con))
    print('claims of lemma:alternate_tile_properties (failing child tiles; smallest word):')
    print('  %-38s %-22s %-22s' % ('claim', 'literal TeX reading', 'constructor'))
    for k in keys:
        a = lit.get(k, [])
        b = con.get(k, [])
        print('  %-38s %4d %-16s %4d %-16s' % (k, len(a), smallest(a), len(b), smallest(b)))


if __name__ == '__main__':
    main(sys.argv[1:])
