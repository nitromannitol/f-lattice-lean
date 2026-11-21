"""Scan simple admissible tiles of lemma:almost_square_tiling and test the Cramer-numerator window bound,
packing P (the keys of the cells mod the lattice are distinct), and the gap clause A.

Encoding follows FLatticePaper/Tiles/AlmostTiling.lean:
  letters 0=one (1,0), 1=i (0,1), 2=negOne (-1,0), 3=negI (0,-1)
  mulI: 0->1,1->2,2->3,3->0 ; mulNegI = mulI^3 ; neg: 0<->2, 1<->3
  hat(w) = reverse(map neg w) ; boundaryWordOf w1 w2 = w1 ++ w2 ++ hat(rev w1) ++ hat(rev w2)
"""
import itertools
import random
import sys
from collections import defaultdict, deque

VEC = {0: (1, 0), 1: (0, 1), 2: (-1, 0), 3: (0, -1)}
MULI = {0: 1, 1: 2, 2: 3, 3: 0}
NEG = {0: 2, 1: 3, 2: 0, 3: 1}


def mulI(x):
    return MULI[x]


def mulNegI(x):
    return MULI[MULI[MULI[x]]]


def hat(w):
    return [NEG[x] for x in w][::-1]


def wsum(w):
    return (sum(VEC[x][0] for x in w), sum(VEC[x][1] for x in w))


def boundary_word(w1, w2):
    return w1 + w2 + hat(w1[::-1]) + hat(w2[::-1])


def ifollowed(k, w):
    n = len(w)
    for j in range(n):
        if w[j] == 1:
            for m in range(k):
                p = j + 1 + m
                if p >= n or w[p] != 0:
                    return False
    return True


def admissible(w):
    if any(x not in (0, 1) for x in w):
        return False
    if not w or w[0] != 0 or w[-1] != 0:
        return False
    if w == w[::-1]:
        return True
    n = len(w)
    # case (b): w = [1,1,i] ++ wt ++ [1], wt palindrome, every i followed by at least one 1
    if n >= 4 and w[:3] == [0, 0, 1] and w[-1] == 0:
        wt = w[3:-1]
        if wt == wt[::-1] and ifollowed(1, w):
            return True
    # case (c): w = [1] ++ wt ++ [1,1,1], wt palindrome, every i followed by at least three 1s
    if n >= 4 and w[-3:] == [0, 0, 0]:
        wt = w[1:-3]
        if wt == wt[::-1] and ifollowed(3, w):
            return True
    return False


def gen_admissible_upto(maxlen):
    out = []
    for n in range(1, maxlen + 1):
        for bits in itertools.product((0, 1), repeat=n):
            w = list(bits)
            if admissible(w):
                out.append(w)
    return out


def cells_of_polygon(verts):
    """Unit cells (lower-left corners) with centre inside the closed polygon given by verts (closed implicitly)."""
    xs = [v[0] for v in verts]
    ys = [v[1] for v in verts]
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    vert_edges = []
    n = len(verts)
    for j in range(n):
        a = verts[j]
        b = verts[(j + 1) % n]
        if a[0] == b[0] and a[1] != b[1]:
            vert_edges.append((a[0], min(a[1], b[1]), max(a[1], b[1])))
    cells = set()
    for a in range(x0, x1):
        for b in range(y0, y1):
            cx, cy = a + 0.5, b + 0.5
            cross = 0
            for (X, lo, hi) in vert_edges:
                if X > cx and lo < cy < hi:
                    cross += 1
            if cross % 2 == 1:
                cells.add((a, b))
    return cells


def cell_edges_with_other(c):
    a, b = c
    return [((a, b), (a + 1, b), (a, b - 1)),
            ((a + 1, b), (a + 1, b + 1), (a + 1, b)),
            ((a + 1, b + 1), (a, b + 1), (a, b + 1)),
            ((a, b + 1), (a, b), (a - 1, b))]


def boundary_edges(S):
    B = set()
    for c in S:
        for (s, e, other) in cell_edges_with_other(c):
            if other not in S:
                B.add((s, e))
    return B


def lower_left_vertex(S):
    verts = set()
    for (a, b) in S:
        for dx in (0, 1):
            for dy in (0, 1):
                verts.add((a + dx, b + dy))
    return min(verts, key=lambda v: (v[1], v[0]))


def edge_connected(S):
    if not S:
        return False
    start = next(iter(S))
    seen = {start}
    dq = deque([start])
    while dq:
        a, b = dq.popleft()
        for nb in ((a + 1, b), (a - 1, b), (a, b + 1), (a, b - 1)):
            if nb in S and nb not in seen:
                seen.add(nb)
                dq.append(nb)
    return len(seen) == len(S)


def det(u, v):
    return u[0] * v[1] - u[1] * v[0]


def analyse(w1, w2):
    """Return None if (w1, w2) does not give a simple admissible tile of the lemma, else a dict of results."""
    if not (admissible(w1) and admissible([mulNegI(x) for x in w2])):
        return None
    W = boundary_word(w1, w2)
    verts = [(0, 0)]
    for x in W:
        vx, vy = verts[-1]
        verts.append((vx + VEC[x][0], vy + VEC[x][1]))
    assert verts[-1] == (0, 0)
    body = verts[:-1]
    if len(set(body)) != len(body):
        return None                       # dropLast nodup fails: not simple
    edges = [(verts[j], verts[j + 1]) for j in range(len(W))]
    if len(set(edges)) != len(edges):
        return None
    S = cells_of_polygon(body)
    if not S:
        return None
    if lower_left_vertex(S) != (0, 0):
        return None                       # the walk does not start at the lower-left vertex
    if set(edges) != boundary_edges(S):
        return None                       # orientation or shape mismatch with IsBoundaryWordAt
    if not edge_connected(S):
        return None
    v1 = (wsum(w1)[0] + 0, wsum(w1)[1] + 1)          # almostV1 = sum w1 + i
    v2 = (wsum(w2)[0] - 1, wsum(w2)[1])              # almostV2 = sum w2 - 1
    D = det(v1, v2)
    if D == 0:
        return {'D': 0, 'bad': True}
    N1 = lambda z: det(z, v2)
    N2 = lambda z: det(v1, z)
    n1 = [N1(z) for z in S]
    n2 = [N2(z) for z in S]
    spread1 = max(n1) - min(n1)
    spread2 = max(n2) - min(n2)
    aD = abs(D)
    window_ok = spread1 < aD and spread2 < aD
    # packing P: keys mod D distinct
    keys = defaultdict(list)
    for z in S:
        k = (N1(z) % aD, N2(z) % aD)
        keys[k].append(z)
    P_ok = all(len(v) == 1 for v in keys.values())
    # gap clause A: for a cell d outside S, adjacent to S across a boundary edge
    def in_surround(u):
        # u = k v1 + k' v2 with |k|,|k'| <= 1, (k,k') != 0
        if N1(u) % D != 0 or N2(u) % D != 0:
            return None
        k = N1(u) // D
        kp = N2(u) // D
        return abs(k) <= 1 and abs(kp) <= 1 and (k, kp) != (0, 0)
    A_ok = True
    A_witness = None
    for c in S:
        for e in ((1, 0), (0, 1), (-1, 0), (0, -1)):
            d = (c[0] + e[0], c[1] + e[1])
            if d in S:
                continue
            # cells t in S with d - t in L: key equality (mod |D|)
            kd = (N1(d) % aD, N2(d) % aD)
            cand = keys.get(kd, [])
            ok = len(cand) == 0
            for t in cand:
                u = (d[0] - t[0], d[1] - t[1])
                r = in_surround(u)
                if r:
                    ok = True
                    break
            if not ok:
                A_ok = False
                if A_witness is None:
                    A_witness = (d, [(t, (d[0] - t[0], d[1] - t[1])) for t in cand])
    return {'D': D, 'Dabs': aD, 'cells': len(S), 'spread1': spread1, 'spread2': spread2,
            'window_ok': window_ok, 'P_ok': P_ok, 'A_ok': A_ok, 'A_witness': A_witness,
            'w1': w1, 'w2': w2, 'v1': v1, 'v2': v2}


def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    adm = gen_admissible_upto(maxlen)
    # w2 side: w2 with admissible(map mulNegI w2); enumerate v admissible then w2 = map mulI v
    adm2 = [[mulI(x) for x in v] for v in adm]
    print('admissible words up to length', maxlen, ':', len(adm), flush=True)
    count = 0
    simple = 0
    win_fail = []
    P_fail = []
    A_fail = []
    tiles = []
    for w1 in adm:
        for w2 in adm2:
            if len(w1) > maxlen or len(w2) > maxlen:
                continue
            r = analyse(w1, w2)
            if r is None:
                continue
            if r.get('bad'):
                continue
            simple += 1
            tiles.append(r)
            if not r['window_ok']:
                win_fail.append(r)
            if not r['P_ok']:
                P_fail.append(r)
            if not r['A_ok']:
                A_fail.append(r)
    print('simple admissible tiles found:', simple)
    print('window bound fails:', len(win_fail))
    print('packing P fails:', len(P_fail))
    print('gap clause A fails:', len(A_fail))
    worst = max(tiles, key=lambda r: max(r['spread1'], r['spread2']) / r['Dabs']) if tiles else None
    if worst:
        print('worst ratio spread/det:', max(worst['spread1'], worst['spread2']) / worst['Dabs'],
              'at w1', worst['w1'], 'w2', worst['w2'], 'D', worst['D'], 'cells', worst['cells'])
    for label, lst in (('window', win_fail), ('P', P_fail), ('A', A_fail)):
        if lst:
            best = min(lst, key=lambda r: (len(r['w1']) + len(r['w2']), r['cells']))
            print('smallest', label, 'counterexample: w1', best['w1'], 'w2', best['w2'], 'D', best['D'],
                  'cells', best['cells'], 'spread1', best['spread1'], 'spread2', best['spread2'],
                  'A_witness', best.get('A_witness'))
    # distribution of max spread / det
    ratios = sorted((max(r['spread1'], r['spread2']) / r['Dabs'], r['w1'], r['w2']) for r in tiles)
    if ratios:
        print('top 5 ratios:')
        for x in ratios[-5:]:
            print('  ', round(x[0], 4), x[1], x[2])


if __name__ == '__main__':
    main()
