"""Task 28: the standard field of 2^k agrees with the near-one even doubled staircase on the whole closed polygon E of its
child: F(z) = V(z + (0, 1)) for every z in E, where V = NearOneBaseCases.paperNearLadderValue at d = 2k + 2 (the tile
values extended by the formula). E equals (tile - (0, 1)) plus the two boundary points (-1, d) and (d + 1, 2d - 2)."""
import permit_local as pl
import open_inputs_check as oc
import twos_even_fit as tf


def main():
    for k in range(1, 6):
        w = tuple([2] * k)
        F, _ = pl.standard(w)
        fr = oc.frame(w)
        d = 2 * k + 2
        x0, x1, y0, y1 = oc.window(fr)
        E = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if oc.in_polygon((x, y), fr)]
        bad = sum(1 for z in E if F(z) != tf.ladder_value(d, (z[0], z[1] + 1)))
        print("2^%d: |E| = %d, points with F(z) != V(z + (0,1)): %d" % (k, len(E), bad))


if __name__ == "__main__":
    main()
