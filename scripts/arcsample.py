"""Task 53 arc conjecture, numerics: do the letter classes and the two sum inequalities alone make a four-arc loop a
row-chain tile? Random pairs (w1, w2): w1 in {E, N}^*, w2 in {N, W}^*; the loop is w1 w2 hat(rev w1) hat(rev w2), starting
at the origin. Each loop is tested for: simple (distinct vertices), and, when simple, the enclosed cell set (parity
of vertical edges) is edge-connected, checkerboard-free and a row chain. Reported with and without the sum filter
S1.y < S2.y and S1.x + S2.x > 0 (S1 = sum w1, S2 = sum w2).
Usage: python3 arcsample.py N MAXLEN SEED"""
import sys, random
from collections import Counter, deque
E, N, W, S = (1, 0), (0, 1), (-1, 0), (0, -1)


def hatrev(w):
    return [(-x, -y) for (x, y) in reversed(w)]


def vsum(w):
    return (sum(x for x, _ in w), sum(y for _, y in w))


def cells_of(loop_edges, xs, ys):
    cells = set()
    for a in range(min(xs) - 1, max(xs) + 1):
        for b in range(min(ys) - 1, max(ys) + 1):
            cnt = 0
            for (p, q) in loop_edges:
                if p[0] == q[0] and min(p[1], q[1]) == b and p[0] <= a:
                    cnt += 1
            if cnt % 2 == 1: cells.add((a, b))
    return cells


def check(w1, w2):
    dirs = w1 + w2 + hatrev(w1) + hatrev(w2)
    pts = [(0, 0)]
    for d in dirs[:-1]:
        pts.append((pts[-1][0] + d[0], pts[-1][1] + d[1]))
    if len(set(pts)) != len(pts): return "not_simple"
    edges = [(pts[k], pts[(k + 1) % len(pts)]) for k in range(len(pts))]
    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    cells = cells_of(edges, xs, ys)
    if not cells: return "empty"
    # row intervals and row-chain
    rows = {}
    for (a, b) in cells: rows.setdefault(b, []).append(a)
    rs = sorted(rows)
    for b in rs:
        v = sorted(rows[b])
        if v != list(range(v[0], v[-1] + 1)): return "row_not_interval"
    if rs != list(range(rs[0], rs[-1] + 1)): return "rows_not_contiguous"
    for b in rs[:-1]:
        a1 = set(rows[b]); a2 = set(rows[b + 1])
        if not (a1 & a2): return "rows_not_overlapping"
    # edge-connected
    start = next(iter(cells)); seen = {start}; dq = deque([start])
    while dq:
        x, y = dq.popleft()
        for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if n in cells and n not in seen: seen.add(n); dq.append(n)
    if len(seen) != len(cells): return "not_connected"
    return "ok"


if __name__ == "__main__":
    n, maxlen, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    random.seed(seed)
    res = {True: Counter(), False: Counter()}
    for _ in range(n):
        w1 = [random.choice([E, N]) for _ in range(random.randint(1, maxlen))]
        w2 = [random.choice([N, W]) for _ in range(random.randint(1, maxlen))]
        S1, S2 = vsum(w1), vsum(w2)
        filt = S1[1] < S2[1] and S1[0] + S2[0] > 0
        res[filt][check(w1, w2)] += 1
    print("with sum filter:", dict(res[True]))
    print("without filter:", dict(res[False]))
