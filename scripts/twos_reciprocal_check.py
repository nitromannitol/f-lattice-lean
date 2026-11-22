"""Task 50: numerical check of the explicit reciprocal field and of the sheet values at the missing instance.

The explicit formula (Lean: TwosReciprocal.reciprocalField_reduction): for d = 2k+3, a deck reduction z = y + i U + j V
with U = (d, 1), V = (1-d, 1+d), y in the tile of stairEven, 2 R(z) = 2 V(y) + 2 j (t(y) + cV) - T j (j-1),
with V(y) = -(y2(y2-1)/2) + min(y1-1, 0) + corner, t(y) = y1 - d y2, cV = -((d+1)d/2) - d, T = d^2 + 2d - 1.
Checked against the prototype field B1(d) (proto2.py) on a box, for d = 5, 7, 9, for every admissible reduction in a window.
Then the sheets of 2^(k+1) at z = (2,8) (k = 1): A(z) = R(Z(z-(1,1))) + h0(z-(1,1)), C(z) = R(Z(z-(0,2))) + h0(z-(0,2)) + z1 - z2,
with Z(x) = (-x2, x1-1) and h0 = harmonicGrid.
"""
import sys
from pathlib import Path

PROTO = Path.home() / "rwc-wc" / "fl" / "proto" / "proto2.py"


def load():
    src = PROTO.read_text()
    ns = {}
    exec(compile(src[:src.index("for L_ in range(1,4):")], "proto2_defs", "exec"), ns)
    return ns


def in_domain(d, y):
    c, r = y
    corner = (c, r) in [(0, 0), (2, d + 1)]
    return (2 - d <= c <= d) and (0 <= r <= d + 1) and (corner or 1 <= c + r <= d + 2)


def tile_value(d, y):
    c, r = y
    corner = 1 if (c, r) in [(0, 0), (2, d + 1)] else 0
    return -(r * (r - 1) // 2) + min(c - 1, 0) + corner


def formula(d, z, i, j):
    U = (d, 1)
    V = (1 - d, 1 + d)
    y = (z[0] - i * U[0] - j * V[0], z[1] - i * U[1] - j * V[1])
    if not in_domain(d, y):
        return None
    cV = -((d + 1) * d // 2) - d
    T = d * d + 2 * d - 1
    twoR = 2 * tile_value(d, y) + 2 * j * ((y[0] - d * y[1]) + cV) - T * j * (j - 1)
    assert twoR % 2 == 0
    return twoR // 2


def main():
    ns = load()
    B1 = ns["B1"]
    h0 = ns["h0"]
    stats = {"points": 0, "no reduction": 0, "inconsistent": 0, "disagree with proto": 0}
    for d in (5, 7, 9):
        F = B1(d)
        for x in range(-12, 13):
            for y in range(-12, 13):
                z = (x, y)
                vals = set()
                for i in range(-6, 7):
                    for j in range(-6, 7):
                        v = formula(d, z, i, j)
                        if v is not None:
                            vals.add(v)
                stats["points"] += 1
                if not vals:
                    stats["no reduction"] += 1
                    continue
                if len(vals) > 1:
                    stats["inconsistent"] += 1
                if vals.pop() != F(z):
                    stats["disagree with proto"] += 1
    print("explicit formula vs prototype B1(d), d = 5, 7, 9:", stats)
    # sheets of 2^2 (k = 1, d = 5) at z = (2, 8)
    R = B1(5)
    z = (2, 8)
    Zs = lambda x: (-x[1], x[0] - 1)
    p1 = (z[0] - 1, z[1] - 1)
    p2 = (z[0] - 0, z[1] - 2)
    A = R(Zs(p1)) + h0(*p1)
    C = R(Zs(p2)) + h0(*p2) + (z[0] - z[1])
    print("k=1, z=(2,8): R(Z(z-(1,1))) =", R(Zs(p1)), " h0(z-(1,1)) =", h0(*p1), " A =", A)
    print("k=1, z=(2,8): R(Z(z-(0,2))) =", R(Zs(p2)), " h0(z-(0,2)) =", h0(*p2), " C =", C)


if __name__ == "__main__":
    main()
