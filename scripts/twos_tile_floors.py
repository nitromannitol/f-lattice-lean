"""Task 31 step 2: deck representatives (i, j) of y_A, y_C in the periodization of G = B1(d), d = 2k+3."""
import sys
import open_inputs_check as oc
import permit_local as pl
from twos_tile_pieces import zone0, zoneH


def deck(F_frame, y):
    fr = F_frame
    n, d, T, U, V = fr.n, fr.d, fr.T, fr.U, fr.V
    a, b, c, h = pl.win((y[0] + y[1]) % 2 == 0, n, d)
    j = -((fr.t(y) - (a - T)) // T)
    i = (fr.sg(y) - c) // T
    yy = (y[0] - i * U[0] - j * V[0], y[1] - i * U[1] - j * V[1])
    return i, j, yy, fr.inE(yy)


def main(k):
    fr_E = oc.frame(tuple([2] * (k + 1)))
    d, dV = 2 * k + 3, 2 * k + 4
    G_frame = pl.Frame(tuple([3] * k))
    print("k=%d: frame n=%d d=%d T=%d U=%s V=%s" % (k, G_frame.n, G_frame.d, G_frame.T, G_frame.U, G_frame.V))
    for z1 in range(-8, 3 * k + 12):
        out = []
        for z2 in range(-60, 4 * k + 30):
            z = (z1, z2)
            if not oc.in_polygon(z, fr_E):
                continue
            yA, yC = (1 - z2, z1 - 2), (2 - z2, z1 - 1)
            if any(zone0(y, d) or zoneH(y, d) for y in (yA, yC)):
                continue
            iA, jA, yA2, okA = deck(G_frame, yA)
            iC, jC, yC2, okC = deck(G_frame, yC)
            out.append("z2=%d A(i=%d,j=%d%s) C(i=%d,j=%d%s)" % (z2, iA, jA, '' if okA else '!', iC, jC, '' if okC else '!'))
        if out:
            print(" z1=%d" % z1)
            for line in out:
                print("   " + line)


if __name__ == "__main__":
    main(int(sys.argv[1]))
