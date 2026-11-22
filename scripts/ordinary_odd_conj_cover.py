"""Task 48: the odd copies against the conjugate lattice transported by the quarter turn.

Fp_w' (the odd output target of w) is the quarter turn Z(x) = (-x2, x1 - 1) of G = standard(swap w) (plus h0), and G is
sewn on E_s = closedPolygon of the frame of swap w, with the lattice Lambda_s = span(mu_s K_s, T_s) of that frame.
For each odd copy site z we test whether some u in Lambda_s (|i|, |j| <= 6) has Z(z) - u in E_s, and also count the
sites that are inside E_s itself. Even outputs are reported for the child lattice as a control.
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402

R = 6


def lattice(fr):
    n, d = fr.n, fr.d
    mu = 1 if (n + d) % 2 == 0 else 2
    return (mu * d, mu * n), (n - d, n + d)


def main():
    copies = m.read_copies(m.DATA)
    st = Counter()
    for cp in copies:
        w, par, slot = cp["word"], cp["parity"], cp["slot"]
        if not cp["sites"] or all(d == 3 for d in w):
            continue
        if par == "odd":
            sw = tuple(m.swap(list(w)))
            fr = m.Frame(list(sw))
            K, T = lattice(fr)
            for (z, h) in cp["sites"]:
                q = (-z[1], z[0] - 1)
                inside = fr.inE(q)
                cover = inside
                if not cover:
                    for i in range(-R, R + 1):
                        for j in range(-R, R + 1):
                            e = (q[0] - i * K[0] - j * T[0], q[1] - i * K[1] - j * T[1])
                            if fr.inE(e):
                                cover = True
                                break
                        if cover:
                            break
                st[("odd", slot, "Z(z) in E_s", inside)] += 1
                st[("odd", slot, "Z(z) covered by Lambda_s", cover)] += 1
        else:
            fr = m.Frame(list(w))
            K, T = lattice(fr)
            for (z, h) in cp["sites"]:
                inside = fr.inE(z)
                st[("even", slot, "z in E (child)", inside)] += 1
    for k in sorted(st, key=str):
        print(k, st[k])


if __name__ == "__main__":
    main()
