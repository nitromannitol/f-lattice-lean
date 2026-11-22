"""Which sheet of which word reproduces a mixed copy, with its translation and slope (task 46).

For a copy tag of a word w, search over all words u (ending in 1 or 2, length at most three), sheets X in {A_u, C_u}, and
translations v in a box, for copy(s) - slope_k . s - X_u(s + v) constant on the copy sites (slope_k: the alternate jet slope).
"""
import itertools
import sys
from sheet_table import copy
from sheets import sheets
from alt_jets import alternate_jets

R = int(sys.argv[1]) if len(sys.argv) > 1 else 12
universe = [u for n in (1, 2, 3) for u in itertools.product((1, 2, 3), repeat=n) if u[-1] in (1, 2)]
SH = {}
for u in universe:
    try:
        A, C, info = sheets(u)
        SH[u] = (A, C)
    except Exception:
        pass


def search(w, tag, k):
    sites = copy[w][tag]
    sl = alternate_jets(w, "even")[k][1]
    hits = []
    for u, (A, C) in SH.items():
        for name, X in [("A", A), ("C", C)]:
            for a in range(-R, R + 1):
                for b in range(-R, R + 1):
                    ks = set(hs - X((s[0] + a, s[1] + b)) - (sl[0] * s[0] + sl[1] * s[1]) for (s, hs) in sites)
                    if len(ks) == 1:
                        hits.append((u, name, (a, b)))
    return hits


if __name__ == "__main__":
    for w, tag, k in [((1,), "slot2", 2), ((1,), "slot1", 1), ((1, 1, 1), "slot2", 2)]:
        hits = search(w, tag, k)
        print(w, tag, "hits (u, sheet, translate):", len(hits), hits[:8], flush=True)
