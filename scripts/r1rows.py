"""Task 55 (R1, cell rows) numerics: for the odd child of a non-base word, the active pieces on each child row and which
pieces attain the left and right ends of the row, grouped by the phase bit (phase b) and the end pattern.
Usage: python3 r1rows.py L"""
import sys
from collections import Counter, defaultdict
from standard_tiles import words, shift, add, texV1Odd, texV1Even, texV2, state, childTiles
from r1cover import pieces_odd, cells, row_intervals

def piece_rows(sets, y):
    out = []
    for i, s in enumerate(sets):
        xs = row_intervals(s, y)
        if xs:
            out.append((xs[0], xs[-1] + 1, i))
    return sorted(out)

def main(L):
    pattern = Counter()
    examples = {}
    for w in words(L):
        if not w or all(x == 3 for x in w) or all(x == 2 for x in w):
            continue
        par, tO, tE = state(w)
        p, q = par
        b = sum(1 for x in w if x == 1) % 2 == 1
        pcs = pieces_odd(b, tO, tE, p, q)
        sets = [cells(t, o) for (t, o) in pcs]
        child = childTiles(w, par, tO, tE)[0]
        ys = sorted({y for (_, y) in child})
        for y in ys:
            rows = piece_rows(sets, y)
            if not rows:
                continue
            Lmin = min(l for l, r, i in rows)
            Rmax = max(r for l, r, i in rows)
            lp = tuple(sorted(i for l, r, i in rows if l == Lmin))
            rp = tuple(sorted(i for l, r, i in rows if r == Rmax))
            active = tuple(i for l, r, i in rows)
            key = (b, lp, rp, active)
            pattern[key] += 1
            examples.setdefault(key, (w, y))
    for key, n in sorted(pattern.items(), key=lambda kv: (kv[0][0], -kv[1])):
        b, lp, rp, active = key
        print(f"phase={int(b)} left={lp} right={rp} active={active} count={n} e.g. {examples[key]}")

if __name__ == "__main__":
    main(int(sys.argv[1]))
