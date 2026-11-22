"""Task 39 recheck (w1 note): the paper's tiles are SITE sets; the cell tile is R2(T), the cells whose four corners lie in T.

Run: python3 alt_cells.py MAXLEN [LOG ...]
  LOG files are the native constructor logs (native_compare.py format); without them only the literal reading is run.

Two readings of the alternate tiles of words of length <= MAXLEN:
  literal      alt_tiles.alt_odd / alt_even (the TeX reading, site sets);
  constructor  the T lines of the logs (site sets).
For each reading and each word, every cell notion is taken on R2(T) (cells are lower-left corners):
  C1 normalised: the lowest cell (row-first, as at.lowest) is the origin;
  C2 row convexity: each row of cells is an interval;
  C3 edge connected and hole free (complement connected in a box one cell larger);
  C4 point symmetry of the cell set;
  C5 rotation identity on cells: cell_rot(R2(T_w)) = shift(R2(T_swapW(w)), tF) with cell_rot(x, y) = (-y-1, x), the
     lower-left corner of the image of the unit square at (x, y) under rot(x, y) = (-y, x). For the constructor the
     translation is reported when it differs from tF (the constructor tiles are not normalised);
  C6 covering: the window cells are covered by the translates of R2(T) under L'(f), with multiplicities.
The site-level results of alt_checks (the earlier finding, on the sites themselves) are printed for comparison.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import alt_tiles as at  # noqa: E402
import alt_checks as ac  # noqa: E402
import native_compare as nc  # noqa: E402


def R2(T):
    """The cells (lower-left corners c) whose four corners c, c+(1,0), c+(0,1), c+(1,1) all lie in T."""
    cells = set()
    for (x, y) in T:
        for cx in (x - 1, x):
            for cy in (y - 1, y):
                if (cx, cy) in cells:
                    continue
                if (cx, cy) in T and (cx + 1, cy) in T and (cx, cy + 1) in T and (cx + 1, cy + 1) in T:
                    cells.add((cx, cy))
    return frozenset(cells)


def cell_rot(C):
    return frozenset((-y - 1, x) for (x, y) in C)


def cell_checks(C):
    """Pass flags of C1 to C4 for a nonempty cell set."""
    if not C:
        return {'C1 normalised': True, 'C2 row convex': True, 'C3 edge connected': True,
                'C3 hole free': True, 'C4 point symmetric': True}
    return {
        'C1 normalised': at.lowest(C) == (0, 0),
        'C2 row convex': ac.row_convex(C)[0],
        'C3 edge connected': ac.edge_connected(C),
        'C3 hole free': ac.hole_free(C),
        'C4 point symmetric': ac.point_symmetric(C)[0],
    }


def rotation_status(Cp, tw, C):
    """'exact' if shift(Cp, tw) = cell_rot(C); 'translation' if they differ by another translation; else 'fail'."""
    R = cell_rot(C)
    if at.shift(Cp, tw) == R:
        return 'exact', None
    t = ac.translation_between(Cp, R)
    if t is None:
        return 'fail', None
    return 'translation', t


def readings(maxlen, logs):
    words = [w for w in ac.words(maxlen) if w != '']
    literal = {}
    for w in words:
        literal[w] = (at.alt_odd(w), at.alt_even(w))
    constructor = {}
    if logs:
        tiles, _ = nc.parse_all(logs)
        for w in ['',] + words:
            if (w, 'altOdd') in tiles and (w, 'altEven') in tiles:
                constructor[w] = (tiles[(w, 'altOdd')], tiles[(w, 'altEven')])
    return literal, constructor


def run_reading(name, tiles_of, words, out, maxlen):
    fails = {}
    coverage = 0
    for w in words:
        if w not in tiles_of:
            continue
        To, Te = tiles_of[w]
        coverage += 1
        for label, T in (('odd', To), ('even', Te)):
            C = R2(T)
            for key, ok in cell_checks(C).items():
                if not ok:
                    fails.setdefault(key, []).append((w, label))
            if C:
                unc, over = ac.covering_multiplicity(C, _f_of(w, label))
                if unc:
                    fails.setdefault('C6 covering uncovered window cells', []).append((w, label, len(unc)))
        P = at.parents_at(w)
        sw = at.swapW(w)
        if sw not in tiles_of:
            continue
        So, Se = tiles_of[sw]
        for label, T, Tp, tw in (('odd', To, Se, at.tF(at.current(P, 'odd'))),
                                 ('even', Te, So, at.tF(at.current(P, 'even')))):
            status, t = rotation_status(R2(Tp), tw, R2(T))
            if status == 'translation':
                fails.setdefault('C5 rotation identity (other translation)', []).append((w, label, t, tw))
            elif status == 'fail':
                fails.setdefault('C5 rotation identity (fails)', []).append((w, label))
    out.append('%s reading: %d words, %d with both tiles present' % (name, len(words), coverage))
    for key in sorted(fails):
        items = fails[key]
        out.append('  %s: %d failures; smallest %s' % (key, len(items), min(items, key=lambda t: (len(t[0]), t[0]))))
    if not fails:
        out.append('  no failures')
    return fails


_F_CACHE = {}


def _f_of(w, label):
    P = at.parents_at(w)
    return at.current(P, label)


def site_level(words, out):
    """The earlier site-level checks of alt_checks, restricted to the words of the run."""
    fails = {}
    for w in words:
        To, Te = at.alt_odd(w), at.alt_even(w)
        for label, T in (('odd', To), ('even', Te)):
            if not at.is_normalised(T):
                fails.setdefault('A1 normalised (site)', []).append((w, label))
            if not ac.row_convex(T)[0]:
                fails.setdefault('A2 row convex (site)', []).append((w, label))
            if not ac.hole_free(T):
                fails.setdefault('A3 hole free (site)', []).append((w, label))
            if not ac.point_symmetric(T)[0]:
                fails.setdefault('A4 point symmetric (site)', []).append((w, label))
    out.append('site-level (the earlier check, on the site sets), literal reading, %d words' % len(words))
    for key in sorted(fails):
        items = fails[key]
        out.append('  %s: %d failures; smallest %s' % (key, len(items), min(items, key=lambda t: (len(t[0]), t[0]))))
    if not fails:
        out.append('  no failures')


def vertex_on_R2(tiles_of, words, out, label_name):
    """C7: IsAlmostTiling's covering clause on vertices, with the cell tile R2(T): every lattice vertex of the window is a
    corner of a cell of some translate of R2(T) under L'(f)."""
    bad = []
    for w in words:
        if w not in tiles_of:
            continue
        To, Te = tiles_of[w]
        P = at.parents_at(w)
        for label, T, f in (('odd', To, at.current(P, 'odd')), ('even', Te, at.current(P, 'even'))):
            unc, _ = ac.vertex_coverage(R2(T), f)
            if unc:
                bad.append((w, label, len(unc), unc[:2]))
    out.append('C7 vertex covering with R2 (%s): %d tiles with uncovered window vertices' % (label_name, len(bad)))
    for item in bad[:6]:
        out.append('     %s' % (item,))


def site_rotation(maxlen, out):
    """A5 on the site sets (the earlier check), for the words of the run."""
    fails = ac.check_alternate(maxlen)
    items = fails.get('A5 rotation identity (tF)', [])
    out.append('site-level A5 rotation identity (tF), literal reading: %d failures' % len(items))
    return {(w, name) for (w, name, t, tw) in items}


def per_word_differences(maxlen, words, out):
    """Which failing (word, tile) pairs change between the site sets and R2(T) (literal reading)."""
    def site_sets(check):
        res = set()
        for w in words:
            To, Te = at.alt_odd(w), at.alt_even(w)
            for label, T in (('odd', To), ('even', Te)):
                if check == 'A1':
                    bad = not at.is_normalised(T)
                elif check == 'A2':
                    bad = not ac.row_convex(T)[0]
                elif check == 'A3':
                    bad = not ac.hole_free(T)
                else:
                    bad = not ac.point_symmetric(T)[0]
                if bad:
                    res.add((w, label))
        return res

    def cell_sets(check):
        res = set()
        for w in words:
            To, Te = at.alt_odd(w), at.alt_even(w)
            for label, T in (('odd', To), ('even', Te)):
                C = R2(T)
                if check == 'A1':
                    bad = not cell_checks(C)['C1 normalised']
                elif check == 'A2':
                    bad = not cell_checks(C)['C2 row convex']
                elif check == 'A3':
                    bad = not cell_checks(C)['C3 hole free']
                else:
                    bad = not cell_checks(C)['C4 point symmetric']
                if bad:
                    res.add((w, label))
        return res

    out.append('per-word comparison, literal reading, site sets against R2(T):')
    for check in ('A1', 'A2', 'A3', 'A4'):
        a, b = site_sets(check), cell_sets(check)
        out.append('  %s: site %d, R2 %d, same pairs %d, only site %s, only R2 %s' % (
            check, len(a), len(b), len(a & b), sorted(a - b)[:4], sorted(b - a)[:4]))


def main(argv):
    maxlen = int(argv[0]) if argv else 3
    logs = argv[1:]
    words = [w for w in ac.words(maxlen) if w != '']
    literal, constructor = readings(maxlen, logs)
    out = []
    site_level(words, out)
    site_rotation(maxlen, out)
    per_word_differences(maxlen, words, out)
    run_reading('literal (R2 of the TeX tiles)', literal, words, out, maxlen)
    vertex_on_R2(literal, words, out, 'literal')
    if constructor:
        run_reading('constructor (R2 of the native tiles)', constructor, words, out, maxlen)
        vertex_on_R2(constructor, words, out, 'constructor')
    else:
        out.append('constructor reading: no log given or no words present')
    print('\n'.join(out))


if __name__ == '__main__':
    main(sys.argv[1:])
