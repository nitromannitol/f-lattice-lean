"""For each ordinary odd alternate output of odd phase (words of length <= 3 ending in 1 or 3): the set of slopes J for which
the output equals Q(w)(y - T) + J . y + c for some translation T in a box and constant c, where Q(w) is the odd target
(quarter turn of H of the swapped word, plus the harmonic grid). Prints the slopes found with the smallest translation.
"""
import sys
import ordinary_tile_check as otc
import alt_plane_check as apc
from odd_donor_jet import Q_of, placed_fit
from seventh_jet import parents_of

words = apc.parse_log(apc.DATA)
R = int(sys.argv[1]); J = int(sys.argv[2])
for e in words:
    w = tuple(e["word"])
    if not apc.ordinary(list(w), "odd") or not e["odd"]:
        continue
    ph = sum(1 for d in w if d == 1) % 2
    if ph == 0:
        continue
    hits = placed_fit(e["odd"], Q_of(list(w)), range(-R, R + 1), range(-J, J + 1))
    slopes = sorted(set(h[1] for h in hits))
    zero = [h for h in hits if h[0] == (0, 0)]
    print(w, "parents", parents_of(w), "slopes (any translation, box)", slopes[:8],
          "| zero-translation hits:", [(h[1], h[2]) for h in zero], flush=True)
