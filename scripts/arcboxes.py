"""Task 53 arc geometry, numerics: bounding boxes of the four monotone arcs of a standard tile's boundary loop.
Arc1 (E/N), arc2 (N/W), arc3 (W/S), arc4 (S/E) meet at the four extreme vertices. We test whether the boxes of opposite
arcs (arc1, arc3) and (arc2, arc4) are disjoint (then opposite arcs cannot cross). Usage: python3 arcboxes.py L"""
import sys
from collections import Counter
from standard_tiles import words, oddTile, evenTile
from arcs import trace, find_start


def box(pts):
    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    return min(xs), max(xs), min(ys), max(ys)


def disjoint(a, b):
    return a[1] < b[0] or b[1] < a[0] or a[3] < b[2] or b[3] < a[2]


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    for w in words(L):
        for name, T in (("odd", oddTile(w)), ("even", evenTile(w))):
            loop = trace(T)
            fs = find_start(loop)
            cnt[(name, "n")] += 1
            if fs is None:
                cnt[(name, "no_arcs")] += 1; continue
            r, (i1, i2, i3) = fs
            n = len(loop)
            verts = [loop[(r + k) % n][0] for k in range(n)]
            arc1 = verts[0:i1 + 1]; arc2 = verts[i1:i2 + 1]
            arc3 = verts[i2:i3 + 1]; arc4 = verts[i3:] + [verts[0]]
            b1, b2, b3, b4 = box(arc1), box(arc2), box(arc3), box(arc4)
            cnt[(name, "arc1_arc3_disjoint")] += disjoint(b1, b3)
            cnt[(name, "arc2_arc4_disjoint")] += disjoint(b2, b4)
    for k in sorted(cnt): print(k, cnt[k])
