#!/usr/bin/env python3
"""Check the output of `lake env lean checks/HeadlineAxiomReport.lean`.

Every `#print axioms` report must be present, name only the three standard axioms, and not mention `sorryAx`.
Any error or warning line fails the check.
"""
import re
import sys

EXPECTED = 5
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def main(path):
    text = open(path, encoding="utf-8").read()
    problems = []
    if re.search(r"^(error|warning):", text, re.M):
        problems.append("the axiom report build emitted an error or a warning")
    reports = REPORT.findall(text)
    if len(reports) != EXPECTED:
        problems.append(f"expected {EXPECTED} axiom reports, saw {len(reports)}")
    for name, axioms in reports:
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        extra = used - STANDARD
        if extra:
            problems.append(f"{name} depends on {sorted(extra)}")
        print(f"{name}: {', '.join(sorted(used))}")
    if "does not depend on any axioms" in text:
        print("note: a report depends on no axioms")
    if problems:
        for p in problems:
            print("FAIL:", p)
        return 1
    print("OK: every headline declaration depends only on propext, Classical.choice and Quot.sound")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
