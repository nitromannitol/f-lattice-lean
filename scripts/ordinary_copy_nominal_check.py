"""Task 44: the nominal agreement hnom of the six copies, and the contacts hcon, from the copy dump.

Inputs: scripts/data/ordinary_copy_dump.log (scripts/ordinary_copy_dump_probe.lean, the six placed copies of each ordinary
schedule, words of length <= 3 without all threes, with heights). Uses scripts/ordinary_copy_sheets.py for the plane objects.

1. hnom at zero translation: copy(s) = planeTarget(s) + g on all sites of the copy, for some constant g.
   planeTarget: standardField(word) for the even output, Fp of the child word+[1] for the odd output.
2. Sheet attainment (even outputs, where the copy is a sheet): on the copy's sites A <= C for slots 2,3 and C <= A for slots 4,5,
   and all copy sites lie in the closed polygon E of the child frame.
3. Contacts: insertions in the schedule order (slot 0 first, then afterFirstStandard), each overlapping the union of the
   copies already placed (nonempty overlap = the chronological contact).
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402

AFTER_FIRST = {"odd": [1, 4, 5, 2, 3], "even": [2, 3, 1, 4, 5]}


def main():
    copies = m.read_copies(m.DATA)
    groups = {}
    for cp in copies:
        groups.setdefault((cp["word"], cp["parity"]), {})[cp["slot"]] = cp
    hnom = Counter()
    attain = Counter()
    contacts = Counter()
    failures = []
    for (w, par), slots in sorted(groups.items(), key=lambda kv: (len(kv[0][0]), kv[0])):
        if all(d == 3 for d in w):
            continue
        # 1. hnom against planeTarget
        target = m.targets(w, par)["T"]
        for slot, cp in sorted(slots.items()):
            ok = m.fits(cp["sites"], target, (0, 0)) is not None
            hnom[(par, slot, ok)] += 1
            if not ok:
                failures.append((''.join(map(str, w)), par, slot))
        # 2. attainment and containment (even outputs)
        if par == "even":
            child = w
            fr = m.Frame(list(child))
            Fp, A, C, M, F = m.parts(child)
            for slot, cp in slots.items():
                pts = [s for s, _ in cp["sites"]]
                attain[("inside E", slot, all(fr.inE(s) for s in pts))] += 1
                if slot in (2, 3):
                    attain[("A<=C", slot, all(A(s) <= C(s) for s in pts))] += 1
                if slot in (4, 5):
                    attain[("C<=A", slot, all(C(s) <= A(s) for s in pts))] += 1
        # 3. contacts in insertion order
        order = [0] + AFTER_FIRST[par]
        occupied = set()
        for i, slot in enumerate(order):
            pts = {s for s, _ in slots[slot]["sites"]}
            if i > 0:
                contacts[("overlap", bool(occupied & pts))] += 1
            occupied |= pts
    print("hnom at zero translation, by (parity, slot, fits):")
    for k in sorted(hnom): print(" ", k, hnom[k])
    print("failures of hnom:", failures)
    print("attainment and containment, even outputs:")
    for k in sorted(attain): print(" ", k, attain[k])
    print("contacts (insertions after the first):", dict(contacts))


if __name__ == "__main__":
    main()
