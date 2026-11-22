"""Task 29: the chain potential of the twos words 2^m (m = 1..5) equals G(s) - G(s + (1,1)) - s_2 with s = (-x_2, x_1 - 1)
and G the standard field of the conjugate 3^(m-1) (the reciprocal field). Checked on a 13 x 13 window of x.
Also prints which sheet attains the minimum on the closed polygon, for m = 2 (A < C, C < A, A = C, outside E)."""
import permit_local as pl
import open_inputs_check as oc
import reflection_pairs as rp


def main():
    for m in range(1, 6):
        w = tuple([2] * m)
        Fp, Xi, off = pl.model(w)
        conj = tuple(pl.swap(pl.odd_birth_prefix(list(w))))
        G, _ = pl.standard(conj)
        bad = 0
        for x1 in range(-6, 7):
            for x2 in range(-6, 7):
                s = (-x2, x1 - 1)
                if Xi((x1, x2)) != G(s) - G((s[0] + 1, s[1] + 1)) - s[1]:
                    bad += 1
        print("2^%d: conj %s, mismatches of Xi = G(s) - G(s+(1,1)) - s_2: %d" % (m, ''.join(map(str, conj)), bad))
    m = 2
    fr, A, C = rp.sheets_of(tuple([2] * m))
    x0, x1, y0, y1 = oc.window(fr)
    print("min pattern for 2^2 (rows y from top to bottom, columns x from left to right):")
    for y in range(y1, y0 - 1, -1):
        row = ""
        for x in range(x0, x1 + 1):
            z = (x, y)
            if not oc.in_polygon(z, fr):
                row += "."
            elif A(z) < C(z):
                row += "A"
            elif C(z) < A(z):
                row += "C"
            else:
                row += "="
        print("%4d %s" % (y, row))


if __name__ == "__main__":
    main()
