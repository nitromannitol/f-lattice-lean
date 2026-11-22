"""Task 31 step 2: row patterns of the tile/tile class of E (A / T=tie / C), in z2 order, per z1."""
import sys
import open_inputs_check as oc
import permit_local as pl
import twos_even_fit as tf
from twos_tile_pieces import zone0, zoneH


def rows(k):
    fr = oc.frame(tuple([2] * (k + 1)))
    d, dV = 2 * k + 3, 2 * k + 4
    G = pl.standard(tuple([3] * k))[0]
    out = {}
    for z1 in range(-8, 3 * k + 12):
        seq = {}
        for z2 in range(-60, 4 * k + 30):
            z = (z1, z2)
            if not oc.in_polygon(z, fr):
                continue
            yA, yC = (1 - z2, z1 - 2), (2 - z2, z1 - 1)
            if any(zone0(y, d) or zoneH(y, d) for y in (yA, yC)):
                continue
            A = G(yA) + pl.h0(z1 - 1, z2 - 1)
            C = G(yC) + pl.h0(z1, z2 - 2) + z1 - z2
            seq[z2] = 'A' if A < C else ('C' if C < A else 'T')
        if seq:
            lo, hi = min(seq), max(seq)
            out[z1] = (lo, ''.join(seq.get(j, '.') for j in range(lo, hi + 1)))
    return out


if __name__ == "__main__":
    for k in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        print("k=%d (d=%d)" % (k, 2 * k + 3))
        for z1, (lo, s) in sorted(rows(k).items()):
            print("  z1=%3d z2>=%3d  %s" % (z1, lo, s))
