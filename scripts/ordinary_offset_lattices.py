"""Task 48: are the jet offsets of the copies in the period lattices?

Even outputs: offset off_k in the child lattice Lambda_w = span(mu K_w, T_w) (the lattice of the sewn field F_w).
Odd outputs: L(off_k) in the conjugate lattice Lambda_s = span(mu_s K_s, T_s) of the swapped word, with L(v) = (-v2, v1), so
that the target Fp_w' has the affine period law of ordinary_conj_period_law.py along v (lattice of the quarter turn).
Control: odd offsets against the child lattice Lambda_w' of w'.
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402
from ordinary_jet_periods import jets  # noqa: E402


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


def main():
    st = Counter()
    seen = set()
    for L in (1, 2, 3):
        import itertools
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w):
                continue
            off_e, _ = jets(w, "even")
            off_o, _ = jets(w, "odd")
            Kw, Tw = lattice(m.Frame(list(w)))
            sw = tuple(m.swap(list(w)))
            Ks, Ts = lattice(m.Frame(list(sw)))
            wp = tuple(w) + (1,)
            Kwp, Twp = lattice(m.Frame(list(wp)))
            for slot in range(6):
                st[("even", slot, "off in child lattice", in_lattice(off_e[slot], Kw, Tw))] += 1
            for slot in range(6):
                v = off_o[slot]
                Lv = (-v[1], v[0])
                st[("odd", slot, "L(off) in conjugate lattice", in_lattice(Lv, Ks, Ts))] += 1
                st[("odd", slot, "control: off in child lattice of w'", in_lattice(v, Kwp, Twp))] += 1
    for k in sorted(st, key=str):
        print(k, st[k])


if __name__ == "__main__":
    main()
