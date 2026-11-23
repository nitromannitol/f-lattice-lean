import sys
from fractions import Fraction as F
from math import gcd
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from even_cover import sources, member, cell_points
from collections import Counter

def pairs(maxden):
    out = []
    for d in range(2, maxden+1):
        for n in range(1, d):
            if (d+n) % 2 != 1 or gcd(d, n) != 1: continue
            for e in range(2, maxden+1):
                for r in range(1, e):
                    if (e+r) % 2 or gcd(e, r) != 1: continue
                    dt = d*r - n*e
                    if dt in (1, -1): out.append((d, n, e, r, dt))
    return out

def box_conds(al, be):
    return {
        'B0 low [0,be]^2': lambda u, v: u <= be and v <= be,
        'B1 high [al,1]^2': lambda u, v: u >= al and v >= al,
        'B2 [be,1]x[0,al]': lambda u, v: u >= be and v <= al,
        'B3 [0,al]x[be,1]': lambda u, v: u <= al and v >= be,
    }

if __name__ == '__main__':
    maxden = int(sys.argv[1])
    flagmode = sys.argv[2]  # 'T' or 'F' or 'both'
    tally = {}
    npairs = 0
    for (d, n, e, r, dt) in pairs(maxden):
        flag = (dt == -1)
        if flagmode == 'T' and not flag: continue
        if flagmode == 'F' and flag: continue
        npairs += 1
        D = 2*d + e; N = 2*n + r
        srcs = sources(d, n, e, r, flag)
        pts = cell_points(D, N)
        for bname, cond in box_conds(F(2*d, D), F(e, D)).items():
            bp = [(z, u, v) for z, u, v in pts if cond(u, v)]
            for i, s in enumerate(srcs):
                if all(member(d, n, e, r, s, z) for z, _, _ in bp):
                    tally.setdefault((flag, bname), Counter())[f'{s[0]}{i}'] += 1
    print('pairs', npairs)
    for k, c in sorted(tally.items(), key=lambda x: (x[0][0], x[0][1])):
        print(k, dict(c))
