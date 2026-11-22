"""Task 42, part 2: the sites by which the constructor's corrected standard tiles miss the TeX standard tiles.

Run: python3 std_diff.py LOG [LOG ...]

For each word of length <= 3 and each standard output (odd, even), the constructor's tile (native log) is compared with the
TeX tile (alt_tiles.std_odd / std_even). For a word whose tiles differ, the sites of the TeX tile that the constructor
misses are listed, with the placed piece(s) of the TeX child formula that contain them (the donor tile, its offset, and
the position of the site relative to the donor tile's own corners), and whether the site is covered by another piece.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import alt_tiles as at  # noqa: E402
import alt_checks as ac  # noqa: E402
import native_compare as nc  # noqa: E402


def pieces(word, parity):
    """The six placed pieces (name, donor, offset) of the TeX child formula of `word` for the given parity."""
    par, tO, tE = at.std_state(word)
    p, q = par[0], par[1]
    flag = at.phase(word) == 1
    if parity == 'odd':
        if flag:
            return [('E', tE, at.V1o(p)), ('E', tE, at.add(at.V1o(p), at.V1e(q))),
                    ('E', tE, at.V2(p)), ('E', tE, at.add(at.V2(p), at.V1e(q))),
                    ('O', tO, (0, 0)), ('O', tO, at.add(at.add(at.V1e(q), at.V1e(q)), at.V2(q)))]
        return [('E', tE, (0, 0)), ('E', tE, at.V1e(q)), ('E', tE, at.add(at.V1o(p), at.V2(p))),
                ('E', tE, at.add(at.add(at.V1o(p), at.V2(p)), at.V1e(q))),
                ('O', tO, at.add(at.V1e(q), at.V1e(q))), ('O', tO, at.V2(q))]
    if flag:
        return [('E', tE, at.V1o(p)), ('E', tE, at.add(at.V2(p), at.V2(p))), ('O', tO, (0, 0)),
                ('O', tO, at.V2(p)), ('O', tO, at.add(at.V1e(q), at.V2(q))),
                ('O', tO, at.add(at.add(at.V1e(q), at.V2(q)), at.V2(p)))]
    return [('E', tE, (0, 0)), ('E', tE, at.add(at.V1o(p), at.add(at.V2(p), at.V2(p)))),
            ('O', tO, at.V1e(q)), ('O', tO, at.add(at.V1e(q), at.V2(p))), ('O', tO, at.V2(q)),
            ('O', tO, at.add(at.V2(q), at.V2(p)))]


def corners(T):
    """The lowest (row-first) and highest (row-first) sites of a tile, and its bounding box."""
    lo = min(T, key=lambda p: (p[1], p[0]))
    hi = max(T, key=lambda p: (p[1], p[0]))
    xs = [p[0] for p in T]
    ys = [p[1] for p in T]
    return lo, hi, (min(xs), min(ys), max(xs), max(ys))


def main(argv):
    tiles, _ = nc.parse_all(argv)
    words = ac.words(3)
    for w in words:
        if w == '':
            continue
        for parity in ('odd', 'even'):
            name = 'stdOdd' if parity == 'odd' else 'stdEven'
            if (w, name) not in tiles:
                continue
            Tc = tiles[(w, name)]
            Ts = frozenset(at.std_odd(w) if parity == 'odd' else at.std_even(w))
            if Tc == Ts:
                continue
            missing = sorted(Ts - Tc)
            extra = sorted(Tc - Ts)
            print('word %s %s: |Ts|=%d |Tc|=%d missing=%s extra=%s' % (w, parity, len(Ts), len(Tc), missing, extra))
            ps = pieces(w, parity)
            for x in missing:
                hits = []
                for idx, (kind, donor, off) in enumerate(ps):
                    y = at.sub(x, off)
                    if y in donor:
                        hits.append((idx, kind, off, y))
                others = [h[0] for h in hits]
                print('   site %s in pieces %s; donor-local positions %s' % (
                    x, others, [(h[1], h[3]) for h in hits]))
                for idx, kind, off, y in hits:
                    donor = ps[idx][1]
                    lo, hi, box = corners(donor)
                    print('      piece %d (%s, offset %s): local %s, donor lowest %s highest %s box %s' % (
                        idx, kind, off, y, lo, hi, box))


if __name__ == '__main__':
    main(sys.argv[1:])
