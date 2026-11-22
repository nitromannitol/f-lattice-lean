"""Task 49: the periods of the even slot-0,1 donor field M_w = min(A, C), numerically.

For each proper even word w (length <= 3): M_w has the periods p = 2K_o (eps = +1) and p = 2K_o + 2T_o (eps = -1), with
their slopes (zero slope for 2K_o; 2*(num_o,-den_o) for 2T_o). We test:
  (a) M(z + p) - M(z) - s.z is constant on the box (the period law of M with the slope of the copy);
  (b) A(z + p) - A(z) - s.z and C(z + p) - C(z) - s.z are each constant, and their constants agree (so that the minimum shifts
      by the same constant as well);
  (c) L(p) lies in the lattice of the conjugate frame: the frame of swap(birth prefix of w), L(v) = (-v2, v1).
Words, parents and jets as in ordinary_jet_periods.py.
"""
import itertools
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402
from ordinary_jet_periods import jets  # noqa: E402

BOX = range(-4, 5)


def lattice(fr):
    n, d = fr.n, fr.d
    mu = 1 if (n + d) % 2 == 0 else 2
    return (mu * d, mu * n), (n - d, n + d)


def in_lattice(u, K, T):
    det = K[0] * T[1] - K[1] * T[0]
    if det == 0:
        return False
    i_num = u[0] * T[1] - u[1] * T[0]
    j_num = K[0] * u[1] - K[1] * u[0]
    return i_num % det == 0 and j_num % det == 0


def constant_on_box(g):
    vals = set()
    for x in BOX:
        for y in BOX:
            vals.add(g((x, y)))
            if len(vals) > 1:
                return None
    return vals.pop()


def main():
    st = Counter()
    for L in (1, 2, 3):
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w) or w[-1] == 2:
                continue   # even ordinary outputs: the last digit is one or three
            Fp, A, C, M, F = m.parts(w)
            off_e, slo_e = jets(w, "even")
            phase = sum(1 for x in w if x == 1) % 2
            # slot 0 offset and slope (2K_o for phase 1; 0 for phase 0), slot 1 offset and slope (2K_o+2T_o or 2T_o)
            k = 0 if phase == 0 else 0
            cases = []
            cases.append(("slot0", off_e[0], slo_e[0]))
            cases.append(("slot1", off_e[1], slo_e[1]))
            k = max(i for i, x in enumerate(w) if x in (1, 2))
            conj = tuple(m.swap(list(w[:k])))
            Kc, Tc = lattice(m.Frame(list(conj)))
            for name, p, s in cases:
                def ginc(f):
                    return lambda z: f((z[0] + p[0], z[1] + p[1])) - f(z) - (s[0] * z[0] + s[1] * z[1])
                cM = constant_on_box(ginc(M))
                cA = constant_on_box(ginc(A))
                cC = constant_on_box(ginc(C))
                st[(name, "M const", cM is not None)] += 1
                st[(name, "A and C const", cA is not None and cC is not None)] += 1
                if cA is not None and cC is not None:
                    st[(name, "same constant A,C", cA == cC)] += 1
                Lp = (-p[1], p[0])
                st[(name, "L(p) in conjugate lattice", in_lattice(Lp, Kc, Tc))] += 1
    for k_ in sorted(st, key=str):
        print(k_, st[k_])


if __name__ == "__main__":
    main()
