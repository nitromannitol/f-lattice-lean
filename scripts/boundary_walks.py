"""Numerical checks for task 52 (simplicity of the boundary walks).

The boundary walk of a standard tile is w1 * w2 * hat(rev w1) * hat(rev w2), from (0,0), with w1 the bottom edge and
w2 the right edge (`oddBottom`, `oddRight`; `evenBottom`, `evenRight` in StandardBoundary.lean). Letters: 'o' = 1,
'i' = i, 'n' = -1, 'm' = -i. Usage:
    python3 boundary_walks.py standard 6      # all standard tiles of words of length <= 6
    python3 boundary_walks.py pairs 5         # arbitrary admissible pairs (w1, w2) of length <= 5
    python3 boundary_walks.py joint 8         # admissible pairs satisfying the sum constraint of the recursion
"""
import itertools
import sys

VEC = {'o': (1, 0), 'i': (0, 1), 'n': (-1, 0), 'm': (0, -1)}
NEG = {'o': 'n', 'i': 'm', 'n': 'o', 'm': 'i'}
MULI = {'o': 'i', 'i': 'n', 'n': 'm', 'm': 'o'}
NEGI = {'o': 'm', 'i': 'o', 'n': 'i', 'm': 'n'}  # multiplication by -i


def base2(k):
    return ['o'] + ['o', 'i'] * (2 * k + 1) + ['o', 'o'], ['o'] + ['o', 'i'] * (2 * k) + ['o', 'o']


def base3(k):
    return ['o', 'o'] * k + ['o', 'i'] + ['o', 'o'] * (k + 1) + ['o'], ['o'] + ['o', 'o'] * (k + 1)


def edge_step(odd, w, v):
    if odd:
        return w + ['i'] + v + ['i'] + v, w + ['i'] + v
    return v + ['i'] + v + ['i'] + w, v + ['i'] + w


def prefix_edges(pre, rO, rE):
    if all(x == 2 for x in pre):
        return base2(len(pre))
    if pre and all(x == 3 for x in pre):
        return base3(len(pre))
    return edge_step(sum(1 for x in pre if x == 1) % 2 == 1, rO, rE)


def bottom(word):
    """The odd and even bottom edges of the recursion word (the register recursion of BottomEdges.lean)."""
    pre, rO, rE = [], [], []
    for x in word:
        e = prefix_edges(pre, rO, rE)
        if x == 1:
            rO, rE = e
        elif x == 2:
            rO = e[0]
        else:
            rE = e[1]
        pre = pre + [x]
    return prefix_edges(pre, rO, rE)


def swap(word):
    return [{1: 1, 2: 3, 3: 2}[x] for x in word]


def hat(w):
    return [NEG[c] for c in w][::-1]


def standard_sides(word):
    """(w1, w2) for the odd and the even tile of the word."""
    ob, eb = bottom(word)
    sw = bottom(swap(word))
    return [((ob, [MULI[c] for c in sw[1]])), ((eb, [MULI[c] for c in sw[0]]))]


def walk_check(w1, w2):
    W = w1 + w2 + hat(w1) + hat(w2)
    x = y = 0
    pts = [(0, 0)]
    for l in W:
        x += VEC[l][0]
        y += VEC[l][1]
        pts.append((x, y))
    closed = pts[-1] == (0, 0)
    simple = len(set(pts[:-1])) == len(pts[:-1])
    return closed, simple


def is_ifb(k, w):
    for j, x in enumerate(w):
        if x == 'i':
            for m in range(k):
                if j + 1 + m >= len(w) or w[j + 1 + m] != 'o':
                    return False
    return True


def admissible(w):
    if any(x not in ('o', 'i') for x in w) or not w or w[0] != 'o' or w[-1] != 'o':
        return False
    if w == w[::-1]:
        return True
    if len(w) >= 3 and w[:3] == ['o', 'o', 'i'] and w[3:-1] == w[3:-1][::-1] and is_ifb(1, w):
        return True
    if len(w) >= 4 and w[-3:] == ['o', 'o', 'o'] and w[1:-3] == w[1:-3][::-1] and is_ifb(3, w):
        return True
    return False


def letters_words(alpha, L):
    for n in range(1, L + 1):
        for t in itertools.product(alpha, repeat=n):
            yield list(t)


def S(w):
    return sum(VEC[c][0] for c in w), sum(VEC[c][1] for c in w)


def main():
    mode, L = sys.argv[1], int(sys.argv[2])
    if mode == 'standard':
        cnt = bad = 0
        for n in range(L + 1):
            for word in itertools.product((1, 2, 3), repeat=n):
                for w1, w2 in standard_sides(list(word)):
                    cnt += 1
                    closed, simple = walk_check(w1, w2)
                    bad += not (closed and simple)
        print("standard tiles", cnt, "not closed or not simple", bad)
    else:
        W1 = [w for w in letters_words(('o', 'i'), L) if admissible(w)]
        W2 = [w for w in letters_words(('i', 'n'), L) if admissible([NEGI[x] for x in w])]
        pairs = [(a, b) for a in W1 for b in W2]
        if mode == 'joint':
            pairs = []
            for a in W1:
                sa = S(a)
                d, n = sa[0], sa[1] + 1
                for b in W2:
                    sb = S(b)
                    if (sb[0] - 1, sb[1]) == (n - d, n + d):
                        pairs.append((a, b))
        bad = [(''.join(a), ''.join(b)) for a, b in pairs if not walk_check(a, b)[1]]
        print(mode, "pairs", len(pairs), "non-simple", len(bad), bad[:5])


if __name__ == '__main__':
    main()
