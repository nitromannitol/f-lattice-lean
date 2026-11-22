"""Task 30: the strip pieces of min(A, C) = V on E for the twos words 2^m (m = k+1).

A = Fp(z-(1,1)), C = Fp(z-(0,2)) + z1 - z2 with Fp = quarterTurn(G), G = reciprocalField k (denominator dG = 2k+3).
y_A = Z(z-(1,1)) = (1-z2, z1-2), y_C = Z(z-(0,2)) = (2-z2, z1-1).
Zero zone of G: 1-dG <= t <= 2dG with t = y1 - dG y2;  harmonic zone: 1-2dG <= s <= 2dG+1 with s = (dG+1)y1 + (dG-1) y2.
V = paperNearLadderValue (2k+4) (z + (0,1)).

Checks: (1) V = C on the zero zone of y_C intersected with E (the zero band); (2) A >= C on the zero zone of y_A and y_C;
(3) the zero band has z1 in {-1,0,1} (printed range)."""
import open_inputs_check as oc
import permit_local as pl
import twos_even_fit as tf


def zone0(y, dG):
    return 1 - dG <= y[0] - dG * y[1] <= 2 * dG


def main():
    for k in range(0, 5):
        m = k + 1
        w = tuple([2] * m)
        fr = oc.frame(w)
        dG, dV = 2 * k + 3, 2 * k + 4
        n_pts, ok_vc, bad, ok_ac, bad_ac, z1s = 0, 0, [], 0, [], set()
        for z1 in range(-6, 7):
            for z2 in range(-40, 41):
                z = (z1, z2)
                if not oc.in_polygon(z, fr):
                    continue
                if not zone0((2 - z2, z1 - 1), dG):
                    continue
                n_pts += 1
                z1s.add(z1)
                C = pl.h0(z1, z2 - 2) + z1 - z2
                if tf.ladder_value(dV, (z1, z2 + 1)) == C:
                    ok_vc += 1
                else:
                    bad.append(z)
                if zone0((1 - z2, z1 - 2), dG):
                    ok_ac += 1 if pl.h0(z1 - 1, z2 - 1) >= C else 0
                    if pl.h0(z1 - 1, z2 - 1) < C:
                        bad_ac.append(z)
        print("k=%d: zero band points %d, V=C on %d (fails %s); A>=C on zero(yA) points: fails %s; z1 values %s"
              % (k, n_pts, ok_vc, bad[:4], bad_ac[:4], sorted(z1s)))


if __name__ == "__main__":
    main()
