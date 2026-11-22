"""Task 46: where the copy sites lie, for the premises of the nominal agreement.

1. Phase one (eps = +1), even outputs, slots 4 and 5: C <= A on the copy sites, the position of the sites (t and sGrade
   against the I1 thresholds), and the reflected points c - z (Psi(c - z) >= 0 needed for the reflected band).
2. Containment: even copy sites in E of the child; odd copy sites in E of the odd child w+[1].
Inputs: scripts/data/ordinary_copy_dump.log, scripts/ordinary_copy_sheets.py (plane objects from proto2.py).
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402


def phase_one_slots_four_five(copies):
    stats = Counter()
    for cp in copies:
        w, par, slot = cp["word"], cp["parity"], cp["slot"]
        if par != "even" or slot not in (4, 5) or not cp["sites"] or all(d == 3 for d in w):
            continue
        fr = m.Frame(list(w))
        if fr.eps != 1:
            continue
        Fp, A, C, M, F = m.parts(w)
        n, d = fr.n, fr.d
        mu = 1 if (n + d) % 2 == 0 else 2
        centre = (mu * d + (n - d) + 1, mu * n + (n + d) - 1)
        t = lambda z: n * z[0] - d * z[1]
        sg = lambda z: (d + n) * z[0] + (d - n) * z[1]
        bound = 2 * (d + n) - 1
        for (z, h) in cp["sites"]:
            stats["sites"] += 1
            stats[("C <= A at z", C(z) <= A(z))] += 1
            stats[("t(z) >= 1 - d", t(z) >= 1 - d)] += 1
            stats[("sGrade(z) > 2(d+n)-1", sg(z) > bound)] += 1
            zr = (centre[0] - z[0], centre[1] - z[1])
            stats[("Psi(centre - z) >= 0", C(zr) - A(zr) >= 0)] += 1
            stats[("t(centre - z) >= 1 - d", t(zr) >= 1 - d)] += 1
    return stats


def containment(copies):
    stats = Counter()
    for cp in copies:
        w, par, slot = cp["word"], cp["parity"], cp["slot"]
        if not cp["sites"] or all(d == 3 for d in w):
            continue
        child = w if par == "even" else tuple(w) + (1,)
        fr = m.Frame(list(child))
        for (z, h) in cp["sites"]:
            stats[(par, "inside E of child", fr.inE(z))] += 1
    return stats


def main():
    copies = m.read_copies(m.DATA)
    print("phase one, slots four and five (even outputs):")
    for k in sorted(phase_one_slots_four_five(copies), key=str):
        print(" ", k, phase_one_slots_four_five(copies)[k])
    print("containment:")
    for k in sorted(containment(copies), key=str):
        print(" ", k, containment(copies)[k])


if __name__ == "__main__":
    main()
