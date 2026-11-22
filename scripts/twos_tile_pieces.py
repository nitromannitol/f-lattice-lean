"""Task 31, step 2: the tile/tile class of E for the twos words 2^(k+1).

A = Fp(z-(1,1)), C = Fp(z-(0,2)) + z1 - z2, Fp = quarterTurn(G), G = B1(d) = standard(3^k), d = 2k+3.
y_A = (1-z2, z1-2), y_C = (2-z2, z1-1). Tile class: y_A and y_C both outside the zero zone and the harmonic zone of G.
V = paperNearLadderValue (2k+4) (z + (0,1)).
Prints, per k: count of tile/tile points of E, failures of min(A,C)=V, the sheet attaining the minimum, and per z1 the z2 extents."""
import sys
import open_inputs_check as oc
import permit_local as pl
import twos_even_fit as tf


def zone0(y, d):
    return 1 - d <= y[0] - d * y[1] <= 2 * d


def zoneH(y, d):
    return 1 - 2 * d <= (d + 1) * y[0] + (d - 1) * y[1] <= 2 * d + 1


def main(kmax):
    for k in range(0, kmax + 1):
        fr = oc.frame(tuple([2] * (k + 1)))
        d, dV = 2 * k + 3, 2 * k + 4
        G = pl.standard(tuple([3] * k))[0]
        cnt, fails, who = 0, [], {}
        ext = {}
        for z1 in range(-8, 10):
            for z2 in range(-60, 4 * k + 30):
                z = (z1, z2)
                if not oc.in_polygon(z, fr):
                    continue
                yA, yC = (1 - z2, z1 - 2), (2 - z2, z1 - 1)
                if any(zone0(y, d) or zoneH(y, d) for y in (yA, yC)):
                    continue
                cnt += 1
                A = G(yA) + pl.h0(z1 - 1, z2 - 1)
                C = G(yC) + pl.h0(z1, z2 - 2) + z1 - z2
                V = tf.ladder_value(dV, (z1, z2 + 1))
                if min(A, C) != V:
                    fails.append(z)
                tag = 'A' if A < C else ('C' if C < A else 'tie')
                who[tag] = who.get(tag, 0) + 1
                lo, hi = ext.get((z1, tag), (z2, z2))
                ext[(z1, tag)] = (min(lo, z2), max(hi, z2))
        print("k=%d d=%d: tile/tile points %d, min(A,C)!=V at %d %s; sheet counts %s"
              % (k, d, cnt, len(fails), fails[:3], who))
        for key in sorted(ext):
            print("   z1=%d %s: z2 in [%d,%d]" % (key[0], key[1], ext[key][0], ext[key][1]))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
