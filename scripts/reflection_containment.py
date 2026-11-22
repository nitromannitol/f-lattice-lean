"""Containment of the reflected harmonic band in the I1 zone (task 26, item 2).

For each eps = -1 word (58 of the 116 proper words of length <= 4): H = E cap {s <= 2L - 1} (harmonic band), the centre
c = kernel + transverse + (1, -1) (child modified deck), R = c - H (the reflected band, inside E since E is invariant).
Counts how many points of R lie in the I1 zone {t >= 1 - d}, and how many words have R inside the zone.
"""
from collections import Counter

import open_inputs_check as oc
import permit_local as pl
import reflection_pairs as rp


def main():
    tot = Counter()
    words_inside = 0
    words = 0
    for w in pl.proper_words(4):
        fr, _, _ = rp.sheets_of(w)
        n, d, eps = fr["n"], fr["d"], fr["eps"]
        if eps != -1:
            continue
        words += 1
        mu = 1 if (n + d) % 2 == 0 else 2
        ker = (mu * d, mu * n)
        tr = (n - d, n + d)
        c = (ker[0] + tr[0] + 1, ker[1] + tr[1] - 1)
        x0, x1, y0, y1 = oc.window(fr)
        pts = [(x, y) for x in range(x0 - 2, x1 + 3) for y in range(y0 - 2, y1 + 3)]
        E = [z for z in pts if oc.in_polygon(z, fr)]
        H = [z for z in E if (d + n) * z[0] + (d - n) * z[1] <= 2 * (d + n) - 1]
        R = [(c[0] - z[0], c[1] - z[1]) for z in H]
        t = lambda z: n * z[0] - d * z[1]
        inzone = [r for r in R if t(r) >= 1 - d]
        tot["H points"] += len(H)
        tot["R points"] += len(R)
        tot["R points in I1 zone"] += len(inzone)
        if len(inzone) == len(R):
            words_inside += 1
    print("eps=-1 words:", words)
    print("words with R inside the I1 zone:", words_inside)
    for k, v in tot.items():
        print(k, v)


if __name__ == "__main__":
    main()
