"""Task 53 arc lemma, forward convention (the Lean boundaryWordOf: w1 ++ w2 ++ (rev w1).hat ++ (rev w2).hat with
(rev w).hat = w.map neg). The loop is w1 w2 (-w1) (-w2) from the origin. S1 = sum w1, S2 = sum w2.
Tested: simple loop, rows [xS(b), xN(b)) nonempty, consecutive overlap, under the sum filter and the corner
conditions (no reversal at the junctions of the cyclic word).
Usage: python3 arcfwd.py MAXLEN"""
import sys, itertools
from collections import Counter
from arcsample import E, N, W, S, vsum

def neg(w): return [(-x, -y) for x, y in w]

def loop_pts(w1, w2):
    dirs = w1 + w2 + neg(w1) + neg(w2)
    pts = [(0, 0)]
    for d in dirs[:-1]:
        pts.append((pts[-1][0] + d[0], pts[-1][1] + d[1]))
    return pts, dirs

def reversal(w1, w2):
    dirs = w1 + w2 + neg(w1) + neg(w2)
    n = len(dirs)
    return any(dirs[k][0] == -dirs[(k + 1) % n][0] and dirs[k][1] == -dirs[(k + 1) % n][1] for k in range(n))

def arc_cols(w1, w2):
    """xN(b) from the up walk w1 w2, and xS(b) from the down walk -w1 -w2 starting at P2 (forward)"""
    xN = {}; pos = (0, 0)
    for d in w1 + w2:
        if d == N: xN[pos[1]] = pos[0]
        pos = (pos[0] + d[0], pos[1] + d[1])
    H = pos[1]
    xS = {}; pos = (vsum(w1)[0] + vsum(w2)[0], H)
    for d in neg(w1) + neg(w2):
        if d == S: xS[pos[1] - 1] = pos[0]
        pos = (pos[0] + d[0], pos[1] + d[1])
    return H, xN, xS

def words_over(letters, maxlen):
    out = [()]
    for L in range(1, maxlen + 1):
        out += list(itertools.product(letters, repeat=L))
    return [list(w) for w in out]

def rows_ok(w1, w2):
    H, xN, xS = arc_cols(w1, w2)
    ne = all(xS[b] < xN[b] for b in range(H))
    ov = all(xS[b + 1] < xN[b] and xS[b] < xN[b + 1] for b in range(H - 1))
    return ne, ov

if __name__ == "__main__":
    L = int(sys.argv[1])
    W1 = [w for w in words_over([E, N], L) if w]
    W2 = [w for w in words_over([N, W], L) if w]
    res = Counter(); bad = []
    for w1 in W1:
        for w2 in W2:
            S1, S2 = vsum(w1), vsum(w2)
            filt = S1[1] < S2[1] and S1[0] + S2[0] > 0
            rev = reversal(w1, w2)
            ne, ov = rows_ok(w1, w2)
            res[(filt, rev, ne, ov)] += 1
            if filt and not rev and not (ne and ov) and len(bad) < 4: bad.append((w1, w2))
    for k in sorted(res): print("filter, reversal, nonempty, overlap", k, res[k])
    print("bad (filter, no reversal):", bad)
