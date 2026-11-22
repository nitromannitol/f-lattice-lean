"""Task 37: the overlaps of the constructor's insertions, from checks/OverlapNative.lean (log lines H, Q, E).

For each schedule (copies in insertion order: copy 0 is the first copy, then the rest), and each insertion k >= 1, the
incoming copy k must meet the union of the earlier copies (OrderedContacts). The canonical site tested here is the anchor
of copy k: its lower-left cell (the origin of the normalised copy, shifted by its translation), which lies in the copy
itself. The script reports, per schedule type, slot k and phase (W_1 parity), whether the anchor lies in the union of the
earlier copies, and which earlier copies contain it.

Usage: python3 overlap_check.py LOG
"""
import sys
from collections import defaultdict


def lexmin(cells):
    # lexLE p q := p.2 < q.2 or (p.2 = q.2 and p.1 <= q.1): the lower-left cell is the least by (y, x)
    return min(cells, key=lambda p: (p[1], p[0]))


def parse(path):
    schedules = []  # list of (label, [frozenset per copy])
    errors = []
    cur = None
    with open(path) as fh:
        for line in fh:
            line = line.rstrip('\n')
            if line.startswith('H '):
                _, label, count = line.split(' ', 2)[0], line.split(' ')[1], line.split(' ')[-1]
                label = ' '.join(line.split(' ')[1:-1])
                cur = (label, [None] * int(count))
                schedules.append(cur)
            elif line.startswith('Q '):
                parts = line.split(' ', 2)
                idx = int(parts[1])
                pts = set()
                if len(parts) > 2 and parts[2]:
                    for c in parts[2].split(';'):
                        x, y = c.split(',')
                        pts.add((int(x), int(y)))
                cur[1][idx] = frozenset(pts)
            elif line.startswith('E'):
                errors.append(line)
    return schedules, errors


def word_and_kind(label):
    parts = label.split(' ')
    return parts[0], ' '.join(parts[1:])


def phase(word):
    return word.count('1') % 2


# The schedules the evaluator builds for each last digit (the table of lemma:global_odometers): the four outputs
# (standard odd, standard even, alternate odd, alternate even) and both correction pairs (all four pieces).
USED = {
    '1': {'ordStdOdd', 'ordStdEven', 'ordAltOdd', 'ordAltEven'},
    '2': {'ordStdOdd', 'corrStdshortEven', 'corrAltlongOdd', 'ordAltEven'},
    '3': {'corrStdshortOdd', 'ordStdEven', 'ordAltOdd', 'corrAltlongEven'},
}
PIECES = {'pieceLshort', 'pieceLlong', 'pieceRshort', 'pieceRlong'}


def used(word, kind):
    d = word[-1]
    return kind in PIECES or kind in USED[d]


def main(path):
    schedules, errors = parse(path)
    print('schedules: %d, error lines: %d' % (len(schedules), len(errors)))
    fails = []
    stats = defaultdict(lambda: [0, 0, 0])  # (kind, k, phase) -> [total, anchor in union, contacts ok]
    anchor_hits = defaultdict(list)
    for label, copies in schedules:
        word, kind = word_and_kind(label)
        if not used(word, kind):
            continue
        if any(c is None for c in copies):
            fails.append(('missing copy', label))
            continue
        occupied = set(copies[0])
        for k in range(1, len(copies)):
            inc = copies[k]
            contact = bool(occupied & inc)
            anchor = lexmin(inc)
            in_union = anchor in occupied
            earlier = [j for j in range(k) if anchor in copies[j]]
            key = (kind, k, phase(word))
            stats[key][0] += 1
            stats[key][1] += in_union
            stats[key][2] += contact
            if not contact:
                fails.append(('no contact', label, k))
            if not in_union:
                anchor_hits[key].append((word, anchor))
            occupied |= inc
    print('insertions without contact: %d' % sum(1 for f in fails if f[0] == 'no contact'))
    print('kind                       k  phase  total  anchor-in-union  contact')
    for key in sorted(stats):
        total, hit, con = stats[key]
        print('%-26s %2d %5d %6d %16d %8d' % (key[0], key[1], key[2], total, hit, con))
    print('insertions whose anchor is not in the earlier union (first few):')
    for key in sorted(anchor_hits):
        if anchor_hits[key]:
            print('  ', key, anchor_hits[key][:3])


if __name__ == '__main__':
    main(sys.argv[1])
