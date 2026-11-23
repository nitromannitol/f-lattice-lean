"""Task 72 (V-block converse, numerics): the conjugate child's free H points and their transport to the parent V path.

Conjugate child (n, d) = (D - N, D + N) of the word's odd parent N/D.  Claims checked on words over {1,2,3} of length <= 4:
 (a) every even free H point w of the conjugate lies on the bottom boundary floor law: w = (2l - b, b), b = floor(2 n l / L),
     L = n + d (checked on all odd coprime children with d <= 25, 815 points);
 (b) the forward transport x = zTurn(w) = (-w2, w1 - 1) of every even free H point is the parent V vertex
     (-b', 2l - 1 - b') with b' = floor((D - N) l / D) and 1 <= l <= D - 1 (so parent_block_mem_freeV applies);
 (c) those images are in the word frame's freeV;
 (d) the images of the odd free H points are in the word frame's freeV except V_p + I = (N - D + 1, N + D - 1) (excVertex).
Usage: python3 scripts/conj_freeH_vpath_check.py [maxlen]
"""
import os, sys, itertools
from math import gcd
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from permit_local import parents, Frame


def T(n, d): return d * d + 2 * d * n - n * n
def tg(n, d, z): return n * z[0] - d * z[1]
def sg(n, d, z): return (d + n) * z[0] + (d - n) * z[1]
def even(z): return (z[0] + z[1]) % 2 == 0


def inE(n, d, z):
    t = tg(n, d, z); s = sg(n, d, z); Tn = T(n, d)
    if even(z):
        return 2 - Tn <= t <= d + n - 2 and 0 <= s <= Tn + 2 * n
    return n - Tn <= t <= d and 2 - d + n <= s <= Tn + d + n - 2


def hSpec(n, d, t):
    return (t % 2 == 0 and 2 <= t <= d + n - 2) or (t % 2 == 1 and n <= t <= d)


def vSpec(n, d, s):
    return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= d + n - 2))


def freeH(n, d, z):
    return inE(n, d, z) and not inE(n, d, (z[0], z[1] - 1)) and hSpec(n, d, tg(n, d, z))


def freeV(n, d, z):
    return inE(n, d, z) and not inE(n, d, (z[0] - 1, z[1])) and vSpec(n, d, sg(n, d, z))


def box(n, d):
    return [(x, y) for x in range(-2 * d - 2, 2 * d + 3) for y in range(-2 * n - 2, 2 * n + 3)]


def zturn(w): return (-w[1], w[0] - 1)


def words(maxlen):
    for L in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            yield w


if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    c = Counter()
    for u in words(maxlen):
        (N, D), _ = parents(u)
        nc, dc = D - N, D + N
        fr = Frame(list(u))
        nw, dw = fr.n, fr.d
        for w in [z for z in box(nc, dc) if freeH(nc, dc, z)]:
            x = zturn(w)
            c['freeH'] += 1
            if even(w):
                c['even'] += 1
                ls = [l for l in range(1, D + 1) if x == (-((D - N) * l // D), 2 * l - 1 - (D - N) * l // D)]
                c['even_on_vpath_l<D' if ls and ls[0] < D else 'even_NOT_on_vpath_l<D'] += 1
                c['even_img_freeV_word' if freeV(nw, dw, x) else 'even_img_NOT_freeV_word'] += 1
            else:
                c['odd'] += 1
                if freeV(nw, dw, x):
                    c['odd_img_freeV_word'] += 1
                elif x == (N - D + 1, N + D - 1):
                    c['odd_img_is_excVertex'] += 1
                else:
                    c['odd_img_OTHER_fail'] += 1
    print(dict(c))
    cc = Counter()
    for d in range(3, 26, 2):
        for n in range(1, d, 2):
            if gcd(n, d) != 1:
                continue
            L = n + d
            for z in box(n, d):
                if freeH(n, d, z) and even(z) and z[1] >= 0:
                    ok = any(z[0] == 2 * l - z[1] and z[1] == (2 * n * l) // L for l in range(-2 * d, 2 * d + 1))
                    cc['floor_law_ok' if ok else 'floor_law_BAD'] += 1
    print("floor law (general children, even free H):", dict(cc))
