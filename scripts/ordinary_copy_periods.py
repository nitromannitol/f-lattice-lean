"""Task 47: periods for the containment-free route, tested numerically on the even children of words of length <= 3.

1. Cover: every copy site of an even output is a child-span translate e - p of a site e in E at which the slot's sheet is the
   minimum (A <= C for slots 2,3; C <= A for slots 4,5). Searched over p = i K + j T with |i|, |j| <= 6.
2. Periodicity of the sheet difference: for the child generators K = mu(d,n), T = (n-d, n+d), whether
   (A - F)(z + p) - (A - F)(z) is independent of z (F = the periodized even standard field, A = sheet A of the child).
   This is the premise needed to transport agreement from e in E to a copy site s = e + p; the check shows it fails.
"""
import itertools
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402


def cover_check(copies):
    st = Counter()
    R = 6
    for cp in copies:
        w, par, slot = cp["word"], cp["parity"], cp["slot"]
        if par != "even" or not cp["sites"] or all(d == 3 for d in w):
            continue
        fr = m.Frame(list(w))
        Fp, A, C, M, F = m.parts(w)
        n, d = fr.n, fr.d
        mu = 1 if (n + d) % 2 == 0 else 2
        K = (mu * d, mu * n)
        T = (n - d, n + d)
        if slot in (2, 3):
            need = lambda e: A(e) <= C(e)
        elif slot in (4, 5):
            need = lambda e: C(e) <= A(e)
        else:
            need = lambda e: True
        for (z, h) in cp["sites"]:
            ok = False
            for i in range(-R, R + 1):
                for j in range(-R, R + 1):
                    e = (z[0] - i * K[0] - j * T[0], z[1] - i * K[1] - j * T[1])
                    if fr.inE(e) and need(e):
                        ok = True
                        break
                if ok:
                    break
            st[("cover", slot, ok)] += 1
    return st


def sheet_difference_check():
    nonconst = Counter()
    for L in (1, 2, 3):
        for w in itertools.product((1, 2, 3), repeat=L):
            if all(x == 3 for x in w):
                continue
            Fp, A, C, M, F = m.parts(w)
            fr = m.Frame(list(w))
            n, d = fr.n, fr.d
            mu = 1 if (n + d) % 2 == 0 else 2
            K = (mu * d, mu * n)
            T = (n - d, n + d)
            diff = lambda z: A(z) - F(z)
            pts = [(x, y) for x in range(-4, 5) for y in range(-4, 5)]
            for name, p in (("K", K), ("T", T)):
                incs = set(diff((z[0] + p[0], z[1] + p[1])) - diff(z) for z in pts)
                nonconst[(name, len(incs) > 1)] += 1
    return nonconst


def main():
    copies = m.read_copies(m.DATA)
    print("cover (child span translate in E with the slot's sheet minimal), even outputs:")
    for k in sorted(cover_check(copies), key=str):
        print(" ", k, cover_check(copies)[k])
    print("sheet difference A - F under the child generators (True = increment depends on z):")
    for k, v in sorted(sheet_difference_check().items(), key=str):
        print(" ", k, v)


if __name__ == "__main__":
    main()
