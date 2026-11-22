"""Summarize the Lean probe scripts/ordinary_copy_probe.lean (task 41).

Reads the two logs in scripts/data/:
  ordinary_copy_normalized.log: one line per word, per parity, one tuple per insertion
      (contact, constant increment on the overlap, overlap size, new size, shift);
  ordinary_copy_pairwise.log: one line per word, per parity, one tuple per pair (i, j) of copies
      (i, (j, (overlap size, increment j - i constant on the overlap))).
The parity used by the constructor as ordinary: digit one uses both; digit two the odd standard; digit three the even.
"""
import re
import sys
from pathlib import Path

DATA = Path(__file__).parent / "data"


def used(word_last: str, parity: str) -> bool:
    return word_last == "one" or (word_last == "two" and parity == "odd") or (word_last == "three" and parity == "even")


def normalized(path: Path):
    ins = contact_false = const_false = used_ins = 0
    used_bad = []
    for line in path.read_text().splitlines():
        m = re.match(r"(\[.*?\]) odd (\d+) (\[.*?\]) \| even (\d+) (\[.*?\])$", line.strip())
        if not m:
            continue
        word = m.group(1)
        last = word.rstrip("]").split(".")[-1]
        for parity, body in (("odd", m.group(3)), ("even", m.group(5))):
            entries = re.findall(r"\((true|false), \((true|false), \((\d+), \((\d+), (-?\d+)\)\)\)\)", body)
            for c, k, _, _, _ in entries:
                ins += 1
                contact_false += c == "false"
                const_false += k == "false"
                if used(last, parity):
                    used_ins += 1
            nb = sum(1 for e in entries if e[1] == "false")
            if used(last, parity) and nb:
                used_bad.append((word.replace("FLatticePaper.Farey.Digit.", ""), parity, nb))
    print(f"normalized: insertions {ins}, contact false {contact_false}, constancy false (all parities) {const_false}")
    print(f"normalized, parities used as ordinary: insertions {used_ins}, nonconstant {used_bad}")


def pairwise(path: Path):
    pairs = nonempty = bad = 0
    used_bad = []
    for line in path.read_text().splitlines():
        if not line.startswith("PAIRS"):
            continue
        word = line.split(" odd ")[0].split("PAIRS ")[1]
        last = word.rstrip("]").split(".")[-1]
        for parity, body in re.findall(r"(odd|even) (\[.*?\])(?= odd| even|$)", line):
            for i, j, size, const in re.findall(r"\((\d+), \((\d+), \((\d+), (true|false)\)\)\)", body):
                pairs += 1
                nonempty += int(size) > 0
                if const == "false":
                    bad += 1
                    if used(last, parity):
                        used_bad.append((word.replace("FLatticePaper.Farey.Digit.", ""), parity, int(i), int(j), int(size)))
    print(f"pairwise: pairs {pairs}, nonempty overlaps {nonempty}, nonconstant overlaps {bad}")
    print(f"pairwise, nonconstant on parities used as ordinary: {used_bad}")


if __name__ == "__main__":
    normalized(DATA / "ordinary_copy_normalized.log")
    pairwise(DATA / "ordinary_copy_pairwise.log")
