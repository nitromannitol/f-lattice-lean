"""Task 49: how far (in box radius) the increment of M_w under the slot-0,1 vectors stays affine-free constant.

For each even ordinary word and slot k in {0,1}: g(w) = M(w + p) - M(w) - s.w with p, s the jet offset and slope of slot k.
The largest radius R in {2,4,6,8} such that g is constant on the box |w_i| <= R. A global period law needs R = 8 for all
(the test is a finite check, not a proof).
"""
import itertools
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402
from ordinary_jet_periods import jets  # noqa: E402


def const_on(g, R):
    vals = set()
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            vals.add(g((x, y)))
            if len(vals) > 1:
                return False
    return True


def main():
    st = Counter()
    for L in (1, 2, 3):
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w) or w[-1] == 2:
                continue
            Fp, A, C, M, F = m.parts(w)
            off, slo = jets(w, "even")
            for k in (0, 1):
                p, s = off[k], slo[k]
                g = lambda z: M((z[0] + p[0], z[1] + p[1])) - M(z) - (s[0] * z[0] + s[1] * z[1])
                best = 0
                for R in (2, 4, 6, 8):
                    if const_on(g, R):
                        best = R
                    else:
                        break
                st[(k, "largest R with constant increment", best)] += 1
    for key in sorted(st, key=str):
        print(key, st[key])


if __name__ == "__main__":
    main()


def sheets_main():
    """The sheets A and C (not their minimum) under the same vectors: radius of constancy, and the two constants."""
    st = Counter()
    for L in (1, 2, 3):
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w) or w[-1] == 2:
                continue
            Fp, A, C, M, F = m.parts(w)
            off, slo = jets(w, "even")
            for k in (0, 1):
                p, s = off[k], slo[k]
                for name, f in (("A", A), ("C", C)):
                    g = lambda z, f=f: f((z[0] + p[0], z[1] + p[1])) - f(z) - (s[0] * z[0] + s[1] * z[1])
                    best = 0
                    for R in (2, 4, 6, 8):
                        if const_on(g, R):
                            best = R
                        else:
                            break
                    st[(k, name, "largest R", best)] += 1
    for key in sorted(st, key=str):
        print(key, st[key])


if __name__ == "__main__":
    sheets_main()
