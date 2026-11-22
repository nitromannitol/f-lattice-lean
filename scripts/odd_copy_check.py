"""The copies of the ordinary odd alternate against its raw target (task 46).

Dump: data/alt_copy_odd_dump.log (alt_copy_odd_probe.lean: copies of ordinaryAlternateSchedule parity odd for the words of length at most
three ending in 1 or 3; raw coordinates). Raw target of w (alternateOddRawTarget w in Lean): Q(w)(x - delta(w)) + slope(w) . x, with
Q(w) = quarter(H(swap w)) + h0, delta(w) = phase(w) (transverse offset of the odd parent minus the kernel offset of the even parent),
slope(w) = (num, -den) of the odd parent in phase one.
"""
import alt_copy_check as acc
from odd_seventh_check import raw_target, ODD_DUMP
from seventh_jet import phase

TAGS = ["first", "seventh", "slot1", "slot2", "slot3", "slot4", "slot5"]
copy = acc.parse_dump(ODD_DUMP)

if __name__ == "__main__":
    for w in sorted([w for w in copy if w and w[-1] in (1, 3) and not all(d == 3 for d in w)], key=lambda t: (len(t), t)):
        Rw = raw_target(w)
        row = []
        for t in TAGS:
            sites = copy[w][t]
            ks = set(hs - Rw(s) for (s, hs) in sites)
            row.append(f"{t}:{'C' if len(ks) == 1 else '-'}")
        print(w, "phase", phase(w), " ".join(row), flush=True)
