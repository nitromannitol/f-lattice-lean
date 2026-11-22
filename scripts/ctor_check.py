"""Task 43: validate the Python constructor port (ctor.py) against native logs (T word name cells lines).

Run: python3 ctor_check.py LOG [LOG ...]
For every word in the logs and each register name (stdOdd, stdEven, altOdd, altEven), the port's register after the word
is compared with the logged set, both normalised to lower-left (translation classes). Prints mismatches and a summary.
"""
import sys

import ctor
import native_compare as nc

NAMES = {'stdOdd': 0, 'stdEven': 1, 'altOdd': 2, 'altEven': 3}


def main(argv):
    tiles, errors = nc.parse_all(argv)
    words = sorted({w for (w, _) in tiles}, key=lambda w: (len(w), w))
    total = ok = 0
    bad = []
    for w in words:
        try:
            out = ctor.output(w)
        except ctor.CtorError as exc:
            bad.append((w, 'error', str(exc)))
            continue
        for name, idx in NAMES.items():
            if (w, name) not in tiles:
                continue
            total += 1
            got = ctor.llc(out[idx]) if out[idx] else frozenset()
            want = ctor.llc(tiles[(w, name)]) if tiles[(w, name)] else frozenset()
            if got == want:
                ok += 1
            else:
                bad.append((w, name, 'got %d sites, want %d sites' % (len(got), len(want))))
    print('words in logs: %d; register comparisons: %d; agreeing: %d' % (len(words), total, ok))
    print('errors in logs: %d' % len(errors))
    for item in bad:
        print('  MISMATCH', repr(item[0]), item[1], item[2])


if __name__ == '__main__':
    main(sys.argv[1:])
