"""Task 37: a canonical overlap site per insertion, as a formula in the frame data.

For each insertion k >= 1 of each schedule the evaluator builds (overlap_check.USED, and all correction pieces), and each
class (schedule kind, k, phase W_1), search for a formula F = base + c_1 K_p + c_2 T_p + c_3 K_q + c_4 T_q + c_5 e_1 + c_6 e_2
with small integers c_i, where
  base is the anchor of copy k (its lower-left cell) or the anchor of an earlier copy j < k or the origin,
  K_f = (den, num) (= v_{f,1} up to the factor 2 of the odd parent), T_f = (num - den, num + den) (= v_{f,2}),
  p, q are the parents of the word (for the standard and alternate children), or of the saved ancestor u (for the correction
  pieces, whose jets are those of correctionJets word = u),
such that F lies in copy k AND in the union of the earlier copies, for every word of the class.

Usage: python3 overlap_formula.py LOG
"""
import itertools
import sys
from collections import defaultdict

import alt_tiles as at
import overlap_check as oc

BOX = range(-2, 3)


def frame(f):
    num, den = f
    return {'K': (den, num), 'T': (num - den, num + den)}


def frame_vectors(P, u_for_pieces=None):
    p, q = P
    fp, fq = frame(p), frame(q)
    return [fp['K'], fp['T'], fq['K'], fq['T'], (1, 0), (0, 1)]


def pieces_frame_word(word, kind):
    """The parents whose frame data a schedule uses: the word's own parents, or those of the saved ancestor for pieces."""
    if kind.startswith('piece'):
        x = word[:-1]
        d = word[-1]
        strip = '2' if d == '2' else '3'
        u = x
        while u and u[-1] == strip:
            u = u[:-1]
        return at.parents_at(u)
    return at.parents_at(word)


def scan_length(word, kind):
    """For the correction pieces: the number of copies of the pure run beyond the saved ancestor (0 for the others)."""
    if not kind.startswith('piece'):
        return 0
    x = word[:-1]
    d = word[-1]
    strip = '2' if d == '2' else '3'
    u = x
    while u and u[-1] == strip:
        u = u[:-1]
    return len(x) - len(u)


def main(path):
    schedules, _ = oc.parse(path)
    classes = defaultdict(list)  # (kind, k, phase) -> list of (word, copies, anchors, P)
    for label, copies in schedules:
        word, kind = oc.word_and_kind(label)
        if not oc.used(word, kind):
            continue
        if any(c is None for c in copies):
            continue
        anchors = [oc.lexmin(c) for c in copies]
        P = pieces_frame_word(word, kind)
        scan = scan_length(word, kind)
        for k in range(1, len(copies)):
            classes[(kind, word[-1], k, oc.phase(word), scan)].append((word, copies, anchors, P))
    print('classes: %d' % len(classes))
    solved = 0
    unsolved = []
    for key in sorted(classes):
        kind, digit, k, ph, scan = key
        items = classes[key]
        best = None
        # candidate bases: anchor of copy k, anchors of the earlier copies, origin
        nbases = k + 1
        for basis_index in range(nbases + 1):
            for coeffs in itertools.product(BOX, repeat=6):
                norm = sum(abs(c) for c in coeffs)
                if best is not None and (norm, basis_index) >= best[0]:
                    continue
                ok = True
                for word, copies, anchors, P in items:
                    if basis_index == nbases:
                        base = (0, 0)
                    elif basis_index == k:
                        base = anchors[k]
                    else:
                        base = anchors[basis_index]
                    fv = frame_vectors(P)
                    site = base
                    for c, v in zip(coeffs, fv):
                        site = (site[0] + c * v[0], site[1] + c * v[1])
                    if site not in copies[k] or not any(site in copies[j] for j in range(k)):
                        ok = False
                        break
                if ok:
                    best = ((norm, basis_index), basis_index, coeffs)
        if best is None:
            unsolved.append(key)
            print('%-20s d=%s s=%d k=%d phase=%d : no formula in the search box (%d words)' % (kind, digit, scan, k, ph, len(items)))
        else:
            solved += 1
            _, bi, coeffs = best
            base = 'origin' if bi == k + 1 else ('anchor(copy %d)' % k if bi == k else 'anchor(copy %d)' % bi)
            names = ['K_p', 'T_p', 'K_q', 'T_q', 'e1', 'e2']
            terms = ' '.join('%+d*%s' % (c, n) for c, n in zip(coeffs, names) if c)
            print('%-20s d=%s s=%d k=%d phase=%d : %s %s  (%d words)' % (kind, digit, scan, k, ph, base, terms or '', len(items)))
    print('solved %d classes, unsolved %d' % (solved, len(unsolved)))


if __name__ == '__main__':
    main(sys.argv[1])
