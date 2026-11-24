"""The archive's pure-2 closed rank (.work/fields/canonical/pure2_initialization/uniform_bulk.py: native, candidate;
rawall.py: free; globalrank.py: HV, freer, bulkr, addresses, deckrank) ported to Python, in the archive's coordinates
(a = 2K+2, native fundamental domain in (x, Y = y+1)). Checks for K = 1..4:
  (a) the native domain has T points (T = 2a^2+4a-2);
  (b) the archive's candidate rule (forced whites) agrees with the forced inputs of twos_signed_e.py on native whites;
  (c) deckrank is Lambda-periodic on samples, and strict on every Phi-flat selected edge (globalrank.py flat_rank, eta = +-1);
  (d) the largest variation |deckrank(i) - deckrank(c)| over selected edges, against the Phi weight M needed for
      R = M*Phi + deckrank to be strict on every selected edge.
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from twos_signed_e import Twos, add, neg  # noqa: E402


def natural(A, x, y):
    Y = y + 1
    h = Y - x
    main = (-1 <= x <= A + 1 and 1 <= Y <= 3 * A - 1 and -1 <= h <= 2 * A + 1
            and not (x == -1 and Y <= A + 1) and not (x == A + 1 and Y >= 2 * A - 1))
    return main or (x == -1 and Y == 2 * A + 1) or (x == A + 1 and Y == A - 1)


def candidate(A, x, y):
    h = y - x
    low = h % 2 == 1 and -1 <= h <= A - 3 and 1 <= x <= A and y != A - 1 and not (h == -1 and x == 1)
    high = h % 2 == 1 and A + 1 <= h <= 2 * A - 1 and 0 <= x <= A - 1 and y != 2 * A - 1 and not (h == 2 * A - 1 and x == A - 1)
    E = h == A - 2 and 2 <= x <= A
    W = h == A and 0 <= x <= A - 2
    guard = low or high or E or W
    dx = 1 if E else (-1 if W else 0)
    if low or high:
        dy = -1 if y < (A - 1 if low else 2 * A - 1) else 1
    else:
        dy = 0
    return guard, (dx, dy)


def HV(A, x, y):
    H = (x == 1 and y == 0) or (2 <= x <= A and y == x - 2) or (x == A + 1 and y == A - 2)
    V = (x == 0 and 0 <= y < A) or (x == -1 and A <= y < 2 * A)
    return H, V


def freer(A, x, y, eta):
    j = 0 if x == 1 else x - 1
    r = y - A
    if eta == 1:
        Hv = 2 * A + 1 if j == 0 else (1 if j == A else 2 * (A + 1 - x))
        Vv = (2 * y - y % 2) if y < A else (2 * r + 1 + r % 2)
    else:
        Hv = 4 if j == 0 else (1 if j == 1 else (6 if j == A else 2 * A + 7 - 2 * x))
        if y == 0:
            Vv = 5
        elif y < A:
            Vv = 2 * A + 3 - 2 * y - y % 2
        elif y == A:
            Vv = 2
        elif y == A + 1:
            Vv = 1
        else:
            Vv = 2 * A + 4 - 2 * r + r % 2
    return Hv, Vv


def bulkr(A, x, y, eta):
    h = y - x
    o = (x + y) % 2
    cen = A - 1 if h <= A - 2 else 2 * A - 1
    off = 2 * A - 2 if h <= A - 2 else 2 * A
    r = off - 2 * abs(y - cen) - o
    if eta == -1:
        r = (1 - o) if y == cen + 1 else r + (1 if y < cen + 1 else 5)
    if eta == 1:
        first = (2 * A - 3) if x == A else (2 * A + 1 - 2 * y)
        mid = 2 * x + 3
    else:
        first = 2 if x == 2 else (2 * A + 6 - 2 * y)
        mid = 2 * A if x == 1 else 2 * x + 4
    if h == -1:
        return first
    if h == A - 1:
        return mid
    return r


ALIAS = [(i, l) for i in (0, -1, 1) for l in (0, -1, 1)]


def addresses(A, X, Y):
    return [(X - i * (A + 1) + 2 * l, Y - i * (A - 1) - 2 * A * l) for i, l in ALIAS]


def deckrank(A, X, Y, eta):
    offers = []
    bulk = []
    for u, v in addresses(A, X, Y):
        H, V = HV(A, u, v)
        hr, vr = freer(A, u, v, eta)
        offers.append((H, hr))
        offers.append((V, vr))
        bulk.append((natural(A, u, v), bulkr(A, u, v, eta)))
    for g, val in offers + bulk:
        if g:
            return val
    return -1000


def check(K):
    t = Twos(K)
    A = t.a
    cl = t.clauses()
    forced, _ = t.forced(cl)
    res = Counter()
    # (a) the native fundamental domain
    native_pts = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    res['native_count'] = len(native_pts)
    res['T'] = t.T
    # (b) candidate vs forced whites on native sites
    for (x, y) in native_pts:
        c = (x, y)
        if t.lap(c) != 0:
            continue
        g, cd = candidate(A, x, y)
        H, V = HV(A, x, y)
        if H or V:
            res['free_white'] += 1
            continue
        mine = t.dirs(1, forced)[t.key(c)]
        if g:
            res['cand_true'] += 1
            if cd != mine:
                res['cand_mismatch'] += 1
        else:
            res['cand_false_forced'] += 1
    # (c), (d) deckrank: periodicity, flat strictness, variation
    U, V_ = (t.d, t.n), (-2, 2 * A)
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)
        for (x, y) in native_pts[:: max(1, len(native_pts) // 40)]:
            for lam in (U, V_):
                if deckrank(A, x + lam[0], y + lam[1], eta) != deckrank(A, x, y, eta):
                    res[('period', eta)] += 1
        flat_bad = 0
        var = 0
        edges = 0
        for (x, y) in native_pts:
            c = (x, y)
            for i in t.retained(dirs, c):
                edges += 1
                rc = deckrank(A, c[0], c[1], eta)
                ri = deckrank(A, i[0], i[1], eta)
                var = max(var, abs(ri - rc))
                if t.chain(eta, i) == t.chain(eta, c) and not ri < rc:
                    flat_bad += 1
        res[('flat_bad', eta)] = flat_bad
        res[('var', eta)] = var
        res[('edges', eta)] = edges
    return res


def window_and_cover(K):
    """(e) every residue class has one candidate-covered native copy; the other native copies are the uncovered whites.
    (f) deckrank strictness on Phi-flat selected edges over a window of translates, not only at native centres."""
    t = Twos(K)
    A = t.a
    forced, _ = t.forced(t.clauses())
    native_pts = [(x, y) for x in range(-1, A + 2) for y in range(-2 * A - 2, 3 * A + 2) if natural(A, x, y)]
    by_key = {}
    for p in native_pts:
        by_key.setdefault(t.key(p), []).append(p)
    covered = {}
    for p in native_pts:
        if t.lap(p) != 0 or any(p == q for q in t.H() + t.V()):
            continue
        g, _ = candidate(A, p[0], p[1])
        if g:
            covered.setdefault(t.key(p), []).append(p)
    uncovered = [p for p in native_pts if t.lap(p) == 0 and p not in t.H() + t.V()
                 and not candidate(A, p[0], p[1])[0]]
    dup_ok = all(t.key(p) in covered for p in uncovered)
    multi = sum(1 for k, ps in by_key.items() if len(ps) > 1)
    out = {'native_classes_with_2_copies': multi, 'uncovered_whites': len(uncovered), 'each_uncovered_has_covered_copy': dup_ok}
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)
        bad = 0
        for x in range(-2 * A, 2 * A + 1):
            for y in range(-4 * A, 4 * A + 1):
                c = (x, y)
                for i in t.retained(dirs, c):
                    if t.chain(eta, i) == t.chain(eta, c) and not deckrank(A, i[0], i[1], eta) < deckrank(A, c[0], c[1], eta):
                        bad += 1
        out[('window_flat_bad', eta)] = bad
    return out


if __name__ == '__main__':
    for K in [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4]:
        w = window_and_cover(K)
        print('K=%d cover: classes with 2 native copies %d, uncovered whites %d, each has a covered copy: %s; '
              'Phi-flat non-strict over window translates eta=+1: %d, eta=-1: %d'
              % (K, w['native_classes_with_2_copies'], w['uncovered_whites'], w['each_uncovered_has_covered_copy'],
                 w[('window_flat_bad', 1)], w[('window_flat_bad', -1)]))
        r = check(K)
        print('K=%d a=%d T=%d native points %d | candidate: free whites %d, candidate-true whites %d, mismatches %d, '
              'candidate-false forced whites %d' % (K, 2 * K + 2, r['T'], r['native_count'], r['free_white'],
                                                   r['cand_true'], r['cand_mismatch'], r['cand_false_forced']))
        for eta in (1, -1):
            print('    eta=%+d: selected edges %d, deckrank periodic failures %d, Phi-flat non-strict %d, '
                  'max |deckrank variation| %d (Phi weight 2d+3 = %d)'
                  % (eta, r[('edges', eta)], r[('period', eta)], r[('flat_bad', eta)], r[('var', eta)], 2 * (2 * K + 3) + 3))
