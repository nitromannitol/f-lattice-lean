"""Slot three of the ordinary even alternate (task 46): the gap classes and the jet of the copy.

The copy (dump tag slot3) is the donor parents.even placed by alternateJets word .even 3 (offset and slope from alt_jets.py).
For each non-base word, the gap G(s) = F(s) - F(s + sigma) on the copy sites; class F-pure (gap <= 1), G-pure (gap = 2), or mixed.
"""
import ordinary_tile_check as otc
import alt_copy_check as acc
from alt_jets import alternate_jets
from odd_donor_jet import H_of
from seventh_jet import phase

ns = otc.load_proto()
standard, Frame = ns["standard"], ns["Frame"]
copy = acc.parse_dump(acc.DUMP)


def classify(w):
    F = standard(tuple(w))[0]
    fr = Frame(list(w))
    sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    gaps = [F(s) - F((s[0] + sig[0], s[1] + sig[1])) for (s, _) in copy[w]["slot3"]]
    if max(gaps) <= 1:
        return "F-pure", sig
    if min(gaps) >= 2:
        return "G-pure", sig
    return "mixed", sig


if __name__ == "__main__":
    for w in sorted([w for w in copy if w and w[-1] in (1, 2) and not all(d == 2 for d in w)], key=lambda t: (len(t), t)):
        cls, sig = classify(w)
        j3 = alternate_jets(w, "even")[3]
        print(w, "phase", phase(w), cls, "sigma", sig, "slot3 jet", j3, flush=True)
