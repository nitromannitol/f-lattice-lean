"""Translates of the sheets A and C of w for the copies that are not single sheets at zero translation (task 46).

For a copy tag of a word w (ending in 1 or 2), search v in a box with copy(s) - X(s + v) constant on its sites, X in {A, C}.
The expected translation for the even-donor copies is v = off_0 - off_k (the donor is the standard field translated by the
slot-zero jet), up to the sheet structure. Prints the translations found, with the alternate jet offset of the slot and the
slot-zero offset of the standard even schedule (phase 1: 2 oddKernel; phase 0: 0).
"""
import sys
from sheet_table import copy
from sheets import sheets
from alt_jets import alternate_jets
from seventh_jet import phase, parents_of

R = int(sys.argv[1]) if len(sys.argv) > 1 else 14
TAGS = {"slot1": 1, "slot2": 2, "slot3": 3, "slot5": 5}


def std0(w):
    if phase(w) == 0:
        return (0, 0)
    (N, D), _ = parents_of(w)
    return (2 * D, 2 * N)


if __name__ == "__main__":
    words = [(1,), (1, 1), (2, 1), (1, 1, 1), (1, 2, 1), (2, 1, 1), (1, 3, 1)]
    for w in words:
        A, C, info = sheets(w)
        off0 = std0(w)
        jets = alternate_jets(w, "even")
        for t, k in TAGS.items():
            sites = copy[w][t]
            hits = []
            for name, X in [("A", A), ("C", C)]:
                for a in range(-R, R + 1):
                    for b in range(-R, R + 1):
                        ks = set(hs - X((s[0] + a, s[1] + b)) for (s, hs) in sites)
                        if len(ks) == 1:
                            hits.append((name, (a, b)))
            expect = (off0[0] - jets[k][0][0], off0[1] - jets[k][0][1])
            print(w, t, "offset", jets[k][0], "expected v = off0 - off", expect, "hits:", hits[:6], flush=True)
