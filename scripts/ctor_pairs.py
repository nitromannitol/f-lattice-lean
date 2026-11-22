"""Task 43: the missing sets D(w) = TeX(w) - ctor(w) (standard registers, TeX frame) as symmetric pairs.

Run: python3 ctor_pairs.py MAXLEN

With low and up the lowest and upper sites of the TeX tile, and sigma(x) = low + up - x the point reflection of the TeX
tile (the TeX tiles are point-symmetric), the script checks: (a) D is sigma-invariant; (b) the set A = {x - low : x in D,
x in the lower half} of pair offsets; and prints A for each word where D is nonempty.
"""
import sys

import ctor
import alt_tiles as at
import alt_checks as ac


def lowest(T):
    return min(T, key=lambda p: (p[1], p[0]))


def upper(T):
    return max(T, key=lambda p: (p[1], p[0]))


def missing_tex_frame(w, parity):
    T = frozenset(at.std_odd(w) if parity == 'odd' else at.std_even(w))
    out = ctor.output(w)
    C = out[0 if parity == 'odd' else 1]
    lo = lowest(T)
    Cf = frozenset((x + lo[0], y + lo[1]) for (x, y) in ctor.llc(C)) if C else frozenset()
    return T, T - Cf


def main(argv):
    maxlen = int(argv[0])
    for parity in ('odd', 'even'):
        nsym = 0
        rows = []
        for w in ac.words(maxlen):
            if not w or all(c == w[0] for c in w) and w[0] != '1':
                continue
            T, M = missing_tex_frame(w, parity)
            if not M:
                continue
            lo, up = lowest(T), upper(T)
            c2 = (lo[0] + up[0], lo[1] + up[1])
            sym = all((c2[0] - x, c2[1] - y) in M for (x, y) in M)
            nsym += sym
            A = sorted((x - lo[0], y - lo[1]) for (x, y) in M if (x, y) < (c2[0] - x, c2[1] - y))
            rows.append((w, sym, len(M), (lo, up), A))
        print('%s: %d words with missing sites; point-symmetric in %d' % (parity, len(rows), nsym))
        for (w, sym, n, (lo, up), A) in rows:
            print('  %-6r sym=%s missing=%d low=%s up=%s pair-offsets(low-frame)=%s' % (w, sym, n, lo, up, A))


if __name__ == '__main__':
    main(sys.argv[1:])
