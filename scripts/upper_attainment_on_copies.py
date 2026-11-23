"""The restated premise UpperAttainmentOn (task 48): on the sites of the slot-k copy of the even standard output of a word, the sites
in the upper part (sGrade > 2(den + num) - 1 of the child frame of the word) satisfy C <= A, with C, A the sheets of
quarterTurnField (standardField (conjWord word)) (sheetC, sheetA, transcribed as in upper_attainment_check.py).

Checks the premise on the dumped even copies (data/ordinary_copy_dump.log, COPY records with parity even, slots 4 and 5) for every word
that has them (words ending in 1 or 3, as the dump probe emits them), reporting eps and the number of upper sites.
"""
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402
import upper_attainment_check as uac  # noqa: E402


def check(copies, slots=(4, 5)):
    per = defaultdict(Counter)
    for cp in copies:
        w, par, slot = tuple(cp["word"]), cp["parity"], cp["slot"]
        if par != "even" or slot not in slots or not cp["sites"]:
            continue
        fr = uac.make_frame(w)
        bound = 2 * (fr["d"] + fr["n"]) - 1
        for (s, _) in cp["sites"]:
            key = (w, slot)
            per[key]["sites"] += 1
            if uac.s_grade(fr, s) > bound:
                per[key]["upper"] += 1
                if fr["sheetC"](s) <= fr["sheetA"](s):
                    per[key]["C<=A"] += 1
                else:
                    per[key]["C>A"] += 1
    return per


if __name__ == "__main__":
    copies = m.read_copies(m.DATA)
    per = check(copies)
    words = sorted({k[0] for k in per}, key=lambda t: (len(t), t))
    print("word, eps, slot, sites, upper sites, C<=A on upper, C>A on upper")
    fails = []
    for w in words:
        fr = uac.make_frame(w)
        for slot in (4, 5):
            c = per.get((w, slot), Counter())
            print(w, "eps", fr["eps"], "slot", slot, "sites", c["sites"], "upper", c["upper"], "C<=A", c["C<=A"], "C>A", c["C>A"])
            if c["C>A"]:
                fails.append((w, slot, c["C>A"]))
    print("words with even copies:", len(words), "failing (word, slot):", fails)
