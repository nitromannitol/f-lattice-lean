"""Check of the sheet exchange under the centre reflection (task 25, the eps = -1 branch of (I2)).

With c = ChildFrame.centre = kernel + transverse + (1, -1) (kernel = mu (d, n), transverse = (n - d, n + d),
mu = 1 if n + d is even else 2) and t(z) = n z1 - d z2, on the 116 proper words of length <= 4 and a window around E:

  A(c - z) = C(z) - t(z) + kappa   and   C(c - z) = A(z) - t(z) + kappa,   kappa = (d + n - T)/2 = symmetryConstant,

with T = d^2 + 2 d n - n^2. Also Psi = C - A satisfies Psi(c - z) = -Psi(z), and E is invariant under z -> c - z.
Output: the number of words on which each identity holds exactly, for eps = +1 and eps = -1.
"""
from collections import Counter

import open_inputs_check as oc
import permit_local as pl
import reflection_pairs as rp


def main():
    res = Counter()
    for w in pl.proper_words(4):
        fr, A, C = rp.sheets_of(w)
        n, d, eps = fr["n"], fr["d"], fr["eps"]
        mu = 1 if (n + d) % 2 == 0 else 2
        ker = (mu * d, mu * n)
        tr = (n - d, n + d)
        c = (ker[0] + tr[0] + 1, ker[1] + tr[1] - 1)
        refl = lambda z: (c[0] - z[0], c[1] - z[1])
        x0, x1, y0, y1 = oc.window(fr)
        pts = [(x, y) for x in range(x0 - 2, x1 + 3) for y in range(y0 - 2, y1 + 3)]
        t = lambda z: n * z[0] - d * z[1]
        T = d * d + 2 * d * n - n * n
        kappa = (d + n - T) // 2
        exA = all(A(refl(z)) == C(z) - t(z) + kappa for z in pts)
        exC = all(C(refl(z)) == A(z) - t(z) + kappa for z in pts)
        antisym = all((C(refl(z)) - A(refl(z))) == -(C(z) - A(z)) for z in pts)
        inE = all(oc.in_polygon(refl(z), fr) for z in pts if oc.in_polygon(z, fr))
        res[(eps, "A(c-z)=C(z)-t+kappa", exA)] += 1
        res[(eps, "C(c-z)=A(z)-t+kappa", exC)] += 1
        res[(eps, "Psi(c-z)=-Psi(z)", antisym)] += 1
        res[(eps, "E invariant", inE)] += 1
    for key in sorted(res):
        print(key, res[key])


if __name__ == "__main__":
    main()
