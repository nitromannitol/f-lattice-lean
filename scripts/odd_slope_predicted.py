"""Test the predicted slope of each odd-phase ordinary alternate output: the transverse slope (num, -den) of its odd parent,
with translations in a box of radius R. Also reports the translations that fit, for the words where they exist."""
import sys
import alt_plane_check as apc
from odd_donor_jet import Q_of, placed_fit
from seventh_jet import parents_of

R = int(sys.argv[1])
words = apc.parse_log(apc.DATA)
for e in words:
    w = tuple(e["word"])
    if not apc.ordinary(list(w), "odd") or not e["odd"]:
        continue
    if sum(1 for d in w if d == 1) % 2 == 0:
        continue
    (N, D), _ = parents_of(w)
    J = (N, -D)
    Q = Q_of(list(w))
    hits = []
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            ok = None
            good = True
            for (y, dy) in e["odd"]:
                k = dy - (Q((y[0] - a, y[1] - b)) + J[0] * y[0] + J[1] * y[1])
                if ok is None:
                    ok = k
                elif k != ok:
                    good = False
                    break
            if good:
                hits.append(((a, b), ok))
    hits.sort(key=lambda h: abs(h[0][0]) + abs(h[0][1]))
    print(w, "odd parent", (N, D), "predicted slope", J, "fits:", len(hits), "nearest:", hits[:2], flush=True)
