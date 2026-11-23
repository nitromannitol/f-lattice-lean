"""Task 74 (odd_zero, corrected): the Lean SeedFields(u).odd_zero with parentN u = (d - n)/2, parentD u = (d + n)/2 from u's CHILD
(n, d) (StrongEstimates.lean). Line: parentN x1 - parentD x2 = 1 - (parentD + parentN) = 1 - d, even x; claim:
quarterTurnField(standardField u) x = 0, i.e. f(x) = F_u(Zx) + h0(x) = 0. Tested on u = w (proper, length <= 3), over E and over a box.
"""
import sys
from collections import Counter
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import permit_local as pl  # noqa: E402
import w1_arc_band_check as ab  # noqa: E402
from w1_boundary_price_check import closed_E  # noqa: E402
from w1_sheet_check import h0  # noqa: E402
from exact_quotient import words  # noqa: E402


def main():
    st = Counter()
    fails = []
    for w in words(3):
        P = ab.cc.params(tuple(w))
        n, d = P['n'], P['d']
        Np = (d - n) // 2
        Dp = (d + n) // 2
        assert (d - n) % 2 == 0
        F, _ = pl.standard(tuple(w))
        R = 3 * (d + n) + 6
        seeds_E = 0
        bad_E = []
        bad_box = []
        for x1 in range(-R, R + 1):
            for x2 in range(-R, R + 1):
                x = (x1, x2)
                if (x1 + x2) % 2 or Np * x1 - Dp * x2 != 1 - d:
                    continue
                f = F((-x2, x1 - 1)) + h0(x)
                if f != 0:
                    bad_box.append((x, f))
                if closed_E(P, x):
                    seeds_E += 1
                    if f != 0:
                        bad_E.append((x, f))
        st[('line has E-seeds', seeds_E > 0)] += 1
        st[('zero on E-seeds', len(bad_E) == 0)] += 1
        st[('zero on whole box line', len(bad_box) == 0)] += 1
        if bad_E:
            fails.append((w, bad_E[:2]))
    for k in sorted(st, key=str):
        print(k, st[k], flush=True)
    for f in fails[:8]:
        print('FAIL', f, flush=True)
    print('DONE', flush=True)


if __name__ == '__main__':
    main()
