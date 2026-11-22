"""Task 48: does the odd target Fp_w' have affine increments under the conjugate periods transported by the quarter turn?

Fp(z) = G(Z z) + h0(z), with Z z = (-z2, z1 - 1), G = standard(swap w) sewn on E_s with lattice Lambda_s = span(mu_s K_s, T_s).
For u in Lambda_s, p = L^{-1} u with L(p) = (-p2, p1), so Z(z + p) = Z z + u.
The period law of G gives G(q + u) - G(q) affine in q for u = K_s, T_s; h0 contributes an affine part when p1 + p2 is even.
Test: g(z) = Fp(z + p) - Fp(z) is affine (second differences vanish) on a box, for p = L^{-1}(K_s), L^{-1}(T_s).
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402

BOX = range(-4, 5)


def lattice(fr):
    n, d = fr.n, fr.d
    mu = 1 if (n + d) % 2 == 0 else 2
    return (mu * d, mu * n), (n - d, n + d)


def affine_increment(Fp, p):
    """True if z -> Fp(z+p) - Fp(z) is affine on the box (second differences vanish)."""
    g = {}
    for x in range(-6, 7):
        for y in range(-6, 7):
            g[(x, y)] = Fp((x + p[0], y + p[1])) - Fp((x, y))
    for x in BOX:
        for y in BOX:
            for dx, dy in ((1, 0), (0, 1)):
                a = (x, y)
                b = (x + dx, y + dy)
                c = (x + 2 * dx, y + 2 * dy)
                if g[c] - 2 * g[b] + g[a] != 0:
                    return False
    return True


def main():
    st = Counter()
    for L in (1, 2, 3):
        import itertools
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w):
                continue
            wp = tuple(w) + (1,)
            Fp = m.parts(wp)[0]
            sw = tuple(m.swap(list(w)))
            fr_s = m.Frame(list(sw))
            K_s, T_s = lattice(fr_s)
            for name, u in (("K_s", K_s), ("T_s", T_s)):
                p = (u[1], -u[0])          # L^{-1}(u): L(p) = (-p2, p1) = u
                st[(name, "p1+p2 even", (p[0] + p[1]) % 2 == 0, "affine", affine_increment(Fp, p))] += 1
    for k in sorted(st, key=str):
        print(k, st[k])


if __name__ == "__main__":
    main()
