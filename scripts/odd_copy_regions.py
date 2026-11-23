"""Where the sheet facts of the copies of the ordinary odd alternate lie (task 47, step 1).

For an odd word w, u = swap w, the standard field of u is F = min(A, C) on the closed polygon of frameAt u (sheets from
ordinary_copy_sheets.parts(u)), with C - A = sheetDiff. The named sheet facts of OddAlternateFacts are comparisons at points of the
frame of u:
  F-branch  (plane slots, phase one slots 1, 3; zero shift in phase zero slot 4 and the coincident copies): A <= C at z;
  G-branch  (phase one slot 4; phase zero slots 1, 3): C <= A at z + sigma;
  raw-type  (phase zero slots 2, 5): the minimum of A and C at z and z + sigma.
Here z = Z(s - delta) for the plane and G-branch facts and z = Z(s) for the zero-shift copies, with Z(y) = (-y2, y1 - 1).
Zones of frame u, with n = child.num, d = child.den: I1 is t(z) >= 1 - d (t = n z1 - d z2); the I2 band is sGrade(z) <= 2(d+n) - 1 (in the
closed polygon, as StarZoneInputs); the upper region is sGrade(z) > 2(d+n) - 1 (UpperAttainment). For each named fact the script counts,
per copy tag and phase, the position of its points against the closed polygon, the comparison that holds, and the zone.
Inputs: scripts/data/alt_copy_odd_dump.log (through odd_copy_check.copy), scripts/ordinary_copy_sheets.py (sheets of frames).
"""
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402
from odd_copy_check import copy as ODD  # noqa: E402
from seventh_jet import phase  # noqa: E402
from alternate_chart import chart_delta  # noqa: E402


def Z(y):
    return (-y[1], y[0] - 1)


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def zone(fr, z):
    n, d = fr.n, fr.d
    bound = 2 * (d + n) - 1
    t = n * z[0] - d * z[1]
    sg = (d + n) * z[0] + (d - n) * z[1]
    if sg > bound:
        return "upper"
    if t >= 1 - d:
        return "I1"
    return "I2"


# the named fact kinds: which point, and the comparison it needs
KIND = {
    ("1", "plane"): "F", ("3", "plane"): "F",
    ("4", "G"): "G",
    ("2", "zero"): "F", ("5", "zero"): "F",
    ("1", "G0"): "G", ("3", "G0"): "G",
    ("2", "raw0"): "min", ("5", "raw0"): "min",
}


WIN = m.NS["win"]


def reduce_pt(fr, z):
    """The periodic reduction of z into the closed polygon E of the frame (proto2 Frame.periodize): y = z - i U - j V."""
    ev = (z[0] + z[1]) % 2 == 0
    a, b, c, h = WIN(ev, fr.n, fr.d)
    T = fr.T
    j = -((fr.t(z) - (a - T)) // T)
    i = (fr.sg(z) - c) // T
    y = (z[0] - i * fr.U[0] - j * fr.V[0], z[1] - i * fr.U[1] - j * fr.V[1])
    assert fr.inE(y), (z, y)
    return y


def classify_point(parts_u, fr, z):
    Fp, A, C, M, F = parts_u
    y = reduce_pt(fr, z)
    a_le_c = A(y) <= C(y)
    c_le_a = C(y) <= A(y)
    return ("outside E" if not fr.inE(z) else "in E", "A<=C" if a_le_c else "", "C<=A" if c_le_a else "", zone(fr, y))


def main():
    words = sorted([w for w in ODD if w and w[-1] in (1, 3) and not all(d == 3 for d in w)], key=lambda t: (len(t), t))
    stats = defaultdict(Counter)
    for w in words:
        ph = phase(w)
        u = tuple(m.swap(list(w)))
        parts_u = m.parts(u)
        fr = m.Frame(list(u))
        delta = chart_delta(w)
        sigma = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
        for tag in ["slot1", "slot2", "slot3", "slot4", "slot5"]:
            k = tag[-1]
            sites = ODD[w][tag]
            if ph == 1:
                fact = {"1": "plane", "3": "plane", "4": "G", "2": "zero", "5": "zero"}[k]
            else:
                fact = {"1": "G0", "3": "G0", "4": "zero", "2": "raw0", "5": "raw0"}[k]
            for (s, _) in sites:
                if fact in ("plane", "G"):
                    z = Z(sub(s, delta))
                elif fact == "zero":
                    z = Z(s)
                else:
                    z = Z(s)
                pts = [("z", z)]
                if fact in ("G", "G0"):
                    pts = [("z+sigma", add(z, sigma))]
                if fact == "min":
                    pts = [("z", Z(s)), ("z+sigma", add(Z(s), sigma))]
                for name, p in pts:
                    key = (ph, tag, fact, name, fr.eps)
                    stats[key][classify_point(parts_u, fr, p)] += 1
    for key in sorted(stats, key=str):
        print(key)
        for sig, cnt in sorted(stats[key].items(), key=lambda kv: -kv[1]):
            print("   ", sig, cnt)


if __name__ == "__main__":
    main()
