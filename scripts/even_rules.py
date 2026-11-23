import sys
from fractions import Fraction as F
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from even_cover import sources, member, cell_points
from even_agg import pairs

def assign(u, v, al, be, flag):
    """Return the list of (source index, point-region) claims; the decomposition of the cell."""
    # returns source index that the rule assigns, or None if the point is in no rectangle
    if not flag:
        if u <= be and v <= be: return [0]
        if u >= al and v >= al: return [1]
        if be <= u and v <= al: return [2] if v <= al/2 else [3]
        if u <= al and be <= v: return [4] if v <= (1+be)/2 else [5]
        return None
    else:
        if u >= al and v <= be: return [4]
        if u <= be and v >= al: return [5]
        if u <= al and v <= al: return [0] if v <= al/2 else [1]
        if u >= be and v >= be: return [2] if v <= (1+be)/2 else [3]
        return None

if __name__ == '__main__':
    maxden = int(sys.argv[1])
    bad = []; cnt = 0; ptsn = 0
    for (d, n, e, r, dt) in pairs(maxden):
        flag = (dt == -1)
        D = 2*d + e; N = 2*n + r
        al, be = F(2*d, D), F(e, D)
        srcs = sources(d, n, e, r, flag)
        cnt += 1
        for z, u, v in cell_points(D, N):
            ptsn += 1
            idx = assign(u, v, al, be, flag)
            if idx is None:
                bad.append(('uncovered-rule', (d,n,e,r,dt), z, u, v)); continue
            if not all(member(d, n, e, r, srcs[i], z) for i in idx):
                bad.append(('not-in-source', (d,n,e,r,dt), z, u, v, idx))
    print('pairs', cnt, 'points', ptsn, 'bad', len(bad))
    for b in bad[:6]: print(b)
