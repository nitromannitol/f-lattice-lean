"""Task 72 (residual check): do rising black pairs ever occur, for either shift sign?

RisingBlackPair (F) (sigma) c i (Lean): i an input of c, lap F c = -1, (F c - F(c+sigma)) odd, lap F (c+sigma) = -1,
and slipIncrement F (F(.+sigma)) c i = (F i - F(i+sigma)) - (F c - F(c+sigma)) = 1.  The hNegTie tied configuration
(tie Psi c = 0, Psi i >= 1) is a rising black pair with sigma = -shortShift, so an empty rising set makes that residual empty.

Usage: python3 scripts/rising_pair_check.py [maxlen]   (words over {1,2,3}, constant-2 and constant-3 words skipped)
"""
import os, sys, itertools
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from permit_local import standard, Frame, parents
from w1_forcing_check import inn, inp, lap


def words(maxlen):
    for L in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            yield w


def increments(u, sign):
    (N, D), _ = parents(u)
    fr = Frame(u)
    eps = fr.eps
    G, _ = standard(tuple(u))
    M = 3 * D + 3
    sh = (sign * 2 * eps * D, sign * 2 * eps * N)
    add = lambda z, v: (z[0] + v[0], z[1] + v[1])
    sl = lambda z: G(z) - G(add(z, sh))
    out = Counter()
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            c = (x, y)
            if not fr.inE(c) or lap(G, c) != -1:
                continue
            cs = add(c, sh)
            if lap(G, cs) != -1 or (G(c) - G(cs)) % 2 != 1:
                continue
            for i in (inn(c), inp(c)):
                if fr.inE(i):
                    out[sl(i) - sl(c)] += 1
    return out


if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    total = {1: Counter(), -1: Counter()}
    n = 0
    for w in words(maxlen):
        n += 1
        for s in (1, -1):
            total[s].update(increments(w, s))
    print("words checked:", n)
    for s in (1, -1):
        print(f"slip increments over all black pairs, sign {s:+d}:", dict(total[s]))
