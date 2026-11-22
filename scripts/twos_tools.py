"""Shared helpers for the twos-family fit scripts (task 28)."""

DIHEDRAL = [((1, 0), (0, 1)), ((-1, 0), (0, 1)), ((1, 0), (0, -1)), ((-1, 0), (0, -1)),
            ((0, 1), (1, 0)), ((0, -1), (1, 0)), ((0, 1), (-1, 0)), ((0, -1), (-1, 0))]


def affine_on(points, r):
    """True if r (a dict point -> integer) is an integer affine function on the points (exact). Uses a non-collinear
    triple of points as the basis."""
    base = None
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            for m in range(j + 1, len(points)):
                (x0, y0), (x1, y1), (x2, y2) = points[i], points[j], points[m]
                det = (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
                if det != 0:
                    base = (points[i], points[j], points[m], det)
                    break
            if base:
                break
        if base:
            break
    if base is None:
        return False
    (x0, y0), (x1, y1), (x2, y2), det = base
    v0, v1, v2 = r[(x0, y0)], r[(x1, y1)], r[(x2, y2)]
    an = (v1 - v0) * (y2 - y0) - (v2 - v0) * (y1 - y0)
    bn = (x1 - x0) * (v2 - v0) - (x2 - x0) * (v1 - v0)
    if an % det or bn % det:
        return False
    a, b = an // det, bn // det
    c = v0 - a * x0 - b * y0
    return all(r[(x, y)] == a * x + b * y + c for (x, y) in points)
