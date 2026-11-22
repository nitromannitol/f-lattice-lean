"""Task 53 row invariant, numerics: the horizontal abutment of the copies of a child, row by row, through the six-cycle.
Cycles (from junction_core): even: 0-2-3-1-5-4-0 (both phases); odd phase 0: 0-1-4-3-2-5-0; odd phase 1: 0-1-5-3-2-4-0.
For each child and each site row y: S_y = copies present in row y. Checks:
 (C) the copies of S_y are connected in the cycle (induced subgraph);
 (E) every cycle edge with both ends in S_y abuts or overlaps in row y.
If (C) and (E) hold, the union of S_y is an interval (connected intervals with abutting edges).
Usage: python3 rowcycle.py L"""
import sys
from collections import Counter
from junctions import copies
from standard_tiles import words
from siterows import row_intervals

CYC = {("even", 0): [(0, 2), (2, 3), (3, 1), (1, 5), (5, 4), (4, 0)],
       ("even", 1): [(0, 2), (2, 3), (3, 1), (1, 5), (5, 4), (4, 0)],
       ("odd", 0): [(0, 1), (1, 4), (4, 3), (3, 2), (2, 5), (5, 0)],
       ("odd", 1): [(0, 1), (1, 5), (5, 3), (3, 2), (2, 4), (4, 0)]}


def connected_in(S, edges):
    S = set(S)
    if not S: return True
    start = min(S); seen = {start}; st = [start]
    while st:
        i = st.pop()
        for a, b in edges:
            for u, v in ((a, b), (b, a)):
                if u == i and v in S and v not in seen:
                    seen.add(v); st.append(v)
    return seen == S


if __name__ == "__main__":
    L = int(sys.argv[1])
    cnt = Counter()
    for w in words(L):
        cs = copies(w)
        if cs is None: continue
        ph = sum(1 for x in w if x == 1) % 2
        for kind in ("odd", "even"):
            pieces = cs[kind]
            edges = CYC[(kind, ph)]
            ri = [row_intervals(P) for P in pieces]
            ys = set()
            for r in ri: ys |= set(r)
            C_ok = E_ok = True
            for y in ys:
                S = [k for k in range(6) if y in ri[k]]
                if not connected_in(S, edges): C_ok = False
                for a, b in edges:
                    if a in S and b in S:
                        la, ra = ri[a][y][0], ri[a][y][1]
                        lb, rb = ri[b][y][0], ri[b][y][1]
                        if max(la, lb) > min(ra, rb) + 1: E_ok = False
            cnt[(kind, ph, "C_connected")] += C_ok
            cnt[(kind, ph, "E_edges_abut")] += E_ok
            cnt[(kind, ph, "n")] += 1
    for k in sorted(cnt): print(k, cnt[k])
