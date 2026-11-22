"""Task 55 (R2) numerics: for a forward four-arc word (w1 in {E,N}*, w2 in {N,W}*) with the sum filter, the region S of
the arc rows (row b in [0, H) is [xS(b), xN(b)) with xN(b) = colN(w1 w2) and xS(b) from the down walk) has, as its
directed boundary edges (cell on the left in S, the other side outside S), exactly the edges of the walk
w1 w2 (-w1) (-w2) from (0,0), each once; and (0,0) is the lower-left vertex of S.
Records the failures by corner conditions and by the lower-left condition.
Usage: python3 r2check.py N MAXLEN SEED"""
import sys, random
from collections import Counter
from arcfwd import arc_cols, neg, reversal, vsum
from arcsample import E, N, W, S

def region_from_arcs(w1, w2):
    H, xN, xS = arc_cols(w1, w2)
    cells = set()
    for b in range(H):
        for a in range(xS[b], xN[b]):
            cells.add((a, b))
    return cells, H, xN, xS

def bdry_edges(cells):
    out = set()
    for (a, b) in cells:
        # bottom: cell below (a, b-1) outside: directed E (a,b)->(a+1,b)
        if (a, b - 1) not in cells: out.add(((a, b), (a + 1, b)))
        # right: (a+1, b) outside: directed N (a+1,b)->(a+1,b+1)
        if (a + 1, b) not in cells: out.add(((a + 1, b), (a + 1, b + 1)))
        # top: (a, b+1) outside: directed W (a+1,b+1)->(a,b+1)
        if (a, b + 1) not in cells: out.add(((a + 1, b + 1), (a, b + 1)))
        # left: (a-1, b) outside: directed S (a,b+1)->(a,b)
        if (a - 1, b) not in cells: out.add(((a, b + 1), (a, b)))
    return out

def walk_edges(w1, w2):
    dirs = w1 + w2 + neg(w1) + neg(w2)
    pts = [(0, 0)]
    for d in dirs[:-1]:
        pts.append((pts[-1][0] + d[0], pts[-1][1] + d[1]))
    edges = [(pts[k], pts[(k + 1) % len(pts)]) for k in range(len(pts))]
    return edges

def lower_left_ok(cells):
    verts = set()
    for (a, b) in cells:
        for v in ((a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)): verts.add(v)
    if (0, 0) not in verts: return False
    return all(v[1] > 0 or (v[1] == 0 and v[0] >= 0) for v in verts)

if __name__ == "__main__":
    n, maxlen, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    random.seed(seed)
    cnt = Counter(); ex = {}
    for _ in range(n):
        w1 = [random.choice([E, N]) for _ in range(random.randint(1, maxlen))]
        w2 = [random.choice([N, W]) for _ in range(random.randint(1, maxlen))]
        S1, S2 = vsum(w1), vsum(w2)
        filt = S1[1] < S2[1] and S1[0] + S2[0] > 0
        if not filt: cnt["nofilter"] += 1; continue
        Ra = (w1[-1] == E and w2[0] == W); Rb = (w2[-1] == N and w1[0] == N)
        cells, H, xN, xS = region_from_arcs(w1, w2)
        be = bdry_edges(cells)
        we = walk_edges(w1, w2)
        same = (be == set(we)) and len(set(we)) == len(we)
        ll = lower_left_ok(cells)
        key = ("Ra" if Ra else "-", "Rb" if Rb else "-", "boundary=walk&nodup" if same else "BOUNDARY FAILS", "lowerleft" if ll else "NOT lowerleft")
        cnt[key] += 1
        if key not in ex: ex[key] = (w1, w2)
    for k in sorted(cnt, key=str): print(k, cnt[k])
    for k, v in ex.items():
        if k[0] == "-" and k[1] == "-": print("example", k, v)
