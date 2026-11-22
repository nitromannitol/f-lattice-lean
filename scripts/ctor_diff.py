"""Task 43 numerics: the Python constructor port (ctor.py) against the TeX registers (alt_tiles), for all words of
length <= MAXLEN.

Run: python3 ctor_diff.py MAXLEN

For each word and each of the four registers (standard odd / even, alternate odd / even), both tiles are normalised to
lower-left. The report lists, per register, the words where they differ, with the sets of TeX-only sites (missing from
the constructor) and constructor-only sites (extra), and whether the constructor's tile is a subset of the TeX tile.
"""
import sys

import ctor
import alt_tiles as at
import alt_checks as ac

REG = ['stdOdd', 'stdEven', 'altOdd', 'altEven']


def tex(word):
    return [at.std_odd(word), at.std_even(word), at.alt_odd(word), at.alt_even(word)]


def main(argv):
    maxlen = int(argv[0])
    words = ac.words(maxlen)
    diffs = {name: [] for name in REG}
    errors = []
    counts = {name: 0 for name in REG}
    for w in words:
        try:
            out = ctor.output(w)
        except ctor.CtorError as exc:
            errors.append((w, str(exc)))
            continue
        T = tex(w)
        for i, name in enumerate(REG):
            counts[name] += 1
            got = ctor.llc(out[i]) if out[i] else frozenset()
            want = ctor.llc(T[i]) if T[i] else frozenset()
            if got != want:
                diffs[name].append((w, sorted(want - got), sorted(got - want)))
    print('words of length <= %d: %d' % (maxlen, len(words)))
    print('constructor errors: %d %s' % (len(errors), errors[:5]))
    for name in REG:
        rows = diffs[name]
        subset = sum(1 for (_, miss, extra) in rows if not extra)
        print('%s: %d of %d words differ from TeX; constructor subset of TeX in %d' % (
            name, len(rows), counts[name], subset))
        for (w, miss, extra) in rows:
            print('   %-6s missing %-40s extra %s' % (repr(w), miss[:6], extra[:6]))


if __name__ == '__main__':
    main(sys.argv[1:])
