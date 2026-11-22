"""Task 53 row invariant, numerics: the row intervals of the placed copies of each child, per row.
For a non-base word w, child kind (odd/even) and phase, and each site row y of the child: the copies k with a nonempty
row y, their row intervals [l_k(y), r_k(y)], which copy attains the minimum left end and the maximum right end, and
whether the copies' intervals overlap or abut (no gap) in row y. Reports the distinct extreme patterns.
Usage: python3 rowcopies.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words
from siterows import row_intervals


def analyse(pieces):
    rows = {}
    rowsets = [row_intervals(P) for P in pieces]
    ys = set()
    for ri in rowsets: ys |= set(ri)
    out = {}
    for y in sorted(ys):
        present = [(k, ri[y][0], ri[y][1]) for k, ri in enumerate(rowsets) if y in ri]
        lmin = min(present, key=lambda t: (t[1], t[0]))[0]
        rmax = max(present, key=lambda t: (t[2], -t[0]))[0]
        iv = sorted(present, key=lambda t: t[1])
        reach = iv[0][2]; abut = True
        for _, l, r in iv[1:]:
            if l > reach + 1: abut = False
            reach = max(reach, r)
        out[y] = (tuple(k for k, _, _ in present), lmin, rmax, abut)
    return out


if __name__ == "__main__":
    L = int(sys.argv[1])
    stats = {}
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            rows = analyse(cs[kind])
            key = (kind, ph)
            st = stats.setdefault(key, Counter())
            st["words"] += 1
            for y, (present, lmin, rmax, abut) in rows.items():
                st["row_abut" if abut else "row_GAP"] += 1
                st[("lmin", lmin)] += 1
                st[("rmax", rmax)] += 1
    blocks = {}
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            rows = analyse(cs[kind])
            ys = sorted(rows)
            for role, idx in (("lmin", 1), ("rmax", 2)):
                seq = [rows[y][idx] for y in ys]
                # number of maximal runs of constant copy index
                runs = 1 + sum(1 for i in range(len(seq) - 1) if seq[i] != seq[i + 1])
                blocks.setdefault((kind, ph, role), Counter())[runs] += 1
    for key in sorted(blocks):
        print("runs", key, sorted(blocks[key].items()))
    for key in sorted(stats):
        print(key, {k: v for k, v in stats[key].items() if not isinstance(k, tuple)})
        print("   left-min copy counts:", sorted((k[1], v) for k, v in stats[key].items() if isinstance(k, tuple) and k[0] == "lmin"))
        print("   right-max copy counts:", sorted((k[1], v) for k, v in stats[key].items() if isinstance(k, tuple) and k[0] == "rmax"))
