#!/usr/bin/env python3
"""Numerical check of the sheet exchange (ChildFrame.SheetExchange, SheetReflection.lean) for proper words of length <= 4 (task 85).

With centre = kernel + transverse + (1, -1) = (n + 1, 2n + d - 1) and symmetry constant kappa = (d + n - T) / 2, the sheets satisfy
  A(centre - z) = C(z) - t(z) + kappa   and   C(centre - z) = A(z) - t(z) + kappa,   t(z) = n z1 - d z2,
on a box of radius 2d + 6, for all 116 proper words of length <= 4 (3.25 million points). The empty word is excluded: it is not proper.
Run from the scripts directory: python3 w1_exchange_check.py
"""
from collections import Counter

import permit_local as P
import w1_tie_check as T


def main(maxlen=4):
    stats = Counter()
    for w in P.proper_words(maxlen):
        G, A, C, M, lv = T.sheet_fields(w)
        fr = P.Frame(list(w))
        n, d, Tq = fr.n, fr.d, fr.T
        centre = (n + 1, 2 * n + d - 1)
        kappa = (d + n - Tq) // 2
        R = 2 * d + 6
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                z = (x, y)
                zc = (centre[0] - x, centre[1] - y)
                t = n * x - d * y
                stats["checked"] += 1
                stats["bad_A"] += int(A(zc) != C(z) - t + kappa)
                stats["bad_C"] += int(C(zc) != A(z) - t + kappa)
        stats["words"] += 1
    print(dict(stats))


if __name__ == "__main__":
    main()
