"""Task 33 numerics: finite checks of the standard and alternate tiles for all words up to a given length.

Run: python3 alt_checks.py MAXLEN
Checks (standard, as a sanity test of the port of StandardTiles.lean):
  S1 normalised (origin is a cell, lexicographically least);
  S2 ChildRot: rot(T(p0)) = shift(T(q0 of swapW w), tF(current odd)), rot(T(q0)) = shift(T(p0 of swapW w), tF(current even)).
Alternate (def:alternate_tiles, PROVISIONAL reading, see alt_tiles.py):
  A1 normalised (origin least, in the tile);
  A2 row convexity (each row is an interval of cells);
  A3 edge-connected (4-connected) and hole-free (complement connected in a box);
  A4 180-degree symmetry (exists c with T = {c - x : x in T});
  A5 rotation identity: rot(T-hat(p0)) = shift(T-hat(q0 of swapW w), tF(current odd)) and the even analogue; the
     translation actually needed is printed when it differs from tF.
"""
import sys
from collections import deque

import alt_tiles as at


def words(maxlen):
    out = ['']
    frontier = ['']
    for _ in range(maxlen):
        nxt = []
        for w in frontier:
            for d in '123':
                nxt.append(w + d)
        out.extend(nxt)
        frontier = nxt
    return out


def row_convex(T):
    rows = {}
    for (x, y) in T:
        rows.setdefault(y, []).append(x)
    for y, xs in rows.items():
        xs = sorted(xs)
        if xs[-1] - xs[0] + 1 != len(xs):
            return False, y
    return True, None


def edge_connected(T):
    if not T:
        return True
    start = next(iter(T))
    seen = {start}
    dq = deque([start])
    while dq:
        x, y = dq.popleft()
        for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if n in T and n not in seen:
                seen.add(n)
                dq.append(n)
    return len(seen) == len(T)


def hole_free(T):
    xs = [p[0] for p in T]
    ys = [p[1] for p in T]
    x0, x1, y0, y1 = min(xs) - 1, max(xs) + 1, min(ys) - 1, max(ys) + 1
    seen = {(x0, y0)}
    dq = deque([(x0, y0)])
    while dq:
        x, y = dq.popleft()
        for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if x0 <= n[0] <= x1 and y0 <= n[1] <= y1 and n not in T and n not in seen:
                seen.add(n)
                dq.append(n)
    return len(seen) == (x1 - x0 + 1) * (y1 - y0 + 1) - len(T)


def point_symmetric(T):
    xs = [p[0] for p in T]
    ys = [p[1] for p in T]
    for cx in range(min(xs) + max(xs) - 2, min(xs) + max(xs) + 3):
        for cy in range(min(ys) + max(ys) - 2, min(ys) + max(ys) + 3):
            if frozenset((cx - x, cy - y) for (x, y) in T) == T:
                return True, (cx, cy)
    return False, None


def translation_between(A, B):
    """A translation t with A + t = B, if one exists."""
    if len(A) != len(B):
        return None
    if not A:
        return (0, 0)
    a = at.lowest(A)
    b = at.lowest(B)
    t = (b[0] - a[0], b[1] - a[1])
    return t if at.shift(A, t) == B else None


def check_standard(maxlen):
    bad = []
    for w in words(maxlen):
        To, Te = at.std_odd(w), at.std_even(w)
        for name, T in (('odd', To), ('even', Te)):
            if not at.is_normalised(T):
                bad.append(('S1', w, name))
        P = at.parents_at(w)
        sw = at.swapW(w)
        if at.rot(To) != at.shift(at.std_even(sw), at.tF(at.current(P, 'odd'))):
            bad.append(('S2odd', w))
        if at.rot(Te) != at.shift(at.std_odd(sw), at.tF(at.current(P, 'even'))):
            bad.append(('S2even', w))
    return bad


def check_alternate(maxlen, verbose=True):
    fails = {}
    trans_report = []
    for w in words(maxlen):
        To, Te = at.alt_odd(w), at.alt_even(w)
        for name, T in (('odd', To), ('even', Te)):
            if not at.is_normalised(T):
                fails.setdefault('A1 normalised', []).append((w, name))
            ok, y = row_convex(T)
            if not ok:
                fails.setdefault('A2 row convex', []).append((w, name, y))
            if not edge_connected(T):
                fails.setdefault('A3 edge connected', []).append((w, name))
            if not hole_free(T):
                fails.setdefault('A3 hole free', []).append((w, name))
            if not point_symmetric(T)[0]:
                fails.setdefault('A4 point symmetric', []).append((w, name))
        if w == '':
            continue
        P = at.parents_at(w)
        sw = at.swapW(w)
        for name, T, Tp, tw in (('odd', To, at.alt_even(sw), at.tF(at.current(P, 'odd'))),
                                ('even', Te, at.alt_odd(sw), at.tF(at.current(P, 'even')))):
            R = at.rot(T)
            if at.shift(Tp, tw) != R:
                t = translation_between(Tp, R)
                fails.setdefault('A5 rotation identity (tF)', []).append((w, name, t, tw))
    return fails


def main(argv):
    maxlen = int(argv[0]) if argv else 3
    bad = check_standard(maxlen)
    print('standard checks (words up to length %d): %d failures' % (maxlen, len(bad)))
    for b in bad[:10]:
        print('  ', b)
    fails = check_alternate(maxlen)
    for key in sorted(fails):
        items = fails[key]
        print('%s: %d failures; smallest %s' % (key, len(items), min(items, key=lambda t: (len(t[0]), t[0]))))
    if not fails:
        print('alternate checks: no failures up to length %d' % maxlen)


if __name__ == '__main__':
    main(sys.argv[1:])


def lattice_gens(f):
    """L'(n/d) generators (paper eq:modified_lattice): v1 = V1 (even) or 2V1 (odd), v2 = V2."""
    n, d = f
    v2 = (n - d, n + d)
    if (n + d) % 2 == 1:
        v1 = (2 * d, 2 * n)
    else:
        v1 = (d, n)
    return v1, v2


def covering_multiplicity(T, f, R=8, W=6):
    """Multiplicity of coverage of the cells in the window [-W, W]^2 by the translates T + k v1 + k' v2, |k|,|k'| <= R."""
    v1, v2 = lattice_gens(f)
    mult = {}
    for k in range(-R, R + 1):
        for kk in range(-R, R + 1):
            t = (k * v1[0] + kk * v2[0], k * v1[1] + kk * v2[1])
            for (x, y) in T:
                c = (x + t[0], y + t[1])
                if -W <= c[0] <= W and -W <= c[1] <= W:
                    mult[c] = mult.get(c, 0) + 1
    cells = [(x, y) for x in range(-W, W + 1) for y in range(-W, W + 1)]
    uncovered = [c for c in cells if c not in mult]
    over = [c for c in cells if mult.get(c, 0) > 1]
    return uncovered, over


def check_covering(maxlen):
    report = []
    for w in words(maxlen):
        if w == '' or is_all_word(w, '2') or is_all_word(w, '3'):
            continue
        P = at.parents_at(w)
        for name, T, f in (('odd', at.alt_odd(w), at.current(P, 'odd')),
                           ('even', at.alt_even(w), at.current(P, 'even'))):
            v1, v2 = lattice_gens(f)
            det = abs(v1[0] * v2[1] - v1[1] * v2[0])
            unc, over = covering_multiplicity(T, f)
            report.append((w, name, len(T), det, len(unc), len(over)))
    return report


def is_all_word(word, digit):
    return len(word) > 0 and all(d == digit for d in word)


def vertex_coverage(T, f, R=8, W=6):
    """IsAlmostTiling's covering clause: every lattice point of the window is a corner of a cell of some translate
    T + k v1 + k' v2 (|k|, |k'| <= R). Returns (uncovered vertices, cell multiplicity > 1 count)."""
    v1, v2 = lattice_gens(f)
    corners = set()
    mult = {}
    for k in range(-R, R + 1):
        for kk in range(-R, R + 1):
            t = (k * v1[0] + kk * v2[0], k * v1[1] + kk * v2[1])
            for (x, y) in T:
                c = (x + t[0], y + t[1])
                mult[c] = mult.get(c, 0) + 1
                for dx in (0, 1):
                    for dy in (0, 1):
                        corners.add((c[0] + dx, c[1] + dy))
    pts = [(x, y) for x in range(-W, W + 1) for y in range(-W, W + 1)]
    unc = [p for p in pts if p not in corners]
    over = [c for c in mult if -W <= c[0] <= W and -W <= c[1] <= W and mult[c] > 1]
    return unc, over


def check_vertex_covering(maxlen):
    out = []
    for w in words(maxlen):
        if w == '' or is_all_word(w, '2') or is_all_word(w, '3'):
            continue
        P = at.parents_at(w)
        for name, T, f in (('odd', at.alt_odd(w), at.current(P, 'odd')),
                           ('even', at.alt_even(w), at.current(P, 'even'))):
            unc, over = vertex_coverage(T, f)
            out.append((w, name, len(unc), len(over), unc[:3]))
    return out
