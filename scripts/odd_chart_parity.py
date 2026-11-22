"""Parity of the odd-alternate chart offset (task 46): is alternateOddChart w EvenSite, i.e. (a1 + a2) even, for odd-parity words?

alternateOddChart w = alternateOddDelta w - alternateOddLowerLeft w, with alternateOddLowerLeft the lexicographic minimum (row, then
column) of the offsets of the six alternate jets and of the seventh copy (its seventh offset plus the restoration). This script
computes the chart from the Python mirror of the Lean definitions (without the restoration, which needs retainedBirth) and reports
the words with an odd coordinate sum.
"""
import itertools
import sys
from alt_jets import alternate_jets, seventh_offset_slope, lexmin
from seventh_jet import parents_of, phase, kernel_jet, transverse_jet


def chart(w, with_restoration=False):
    (N, D), (nq, dq) = parents_of(w)
    ph = phase(w)
    delta = ((N - D) - dq, (N + D) - nq) if ph == 1 else (0, 0)
    offs = [j[0] for j in alternate_jets(w, "odd")] + [seventh_offset_slope(w, "odd")[0]]
    LL = lexmin(offs)
    return (delta[0] - LL[0], delta[1] - LL[1]), LL, delta


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    bad = []
    count = 0
    for n in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=n):
            if w[-1] not in (1, 3):
                continue
            count += 1
            a, LL, delta = chart(w)
            if (a[0] + a[1]) % 2 != 0:
                bad.append((w, a, LL, delta, phase(w)))
    print("odd-parity words up to length", maxlen, ":", count, "; with odd coordinate sum:", len(bad))
    for b in bad[:20]:
        print(b)
