from fractions import Fraction as F
from math import gcd
import itertools, sys

def inH(num, den, z):
    z1, z2 = z
    ev = (z1 + z2) % 2 == 0
    mu = 2 if (num + den) % 2 == 1 else 1
    T = den*den + 2*den*num - num*num
    a = (min(2*num, den-num) if ev else num)
    l = (0 if ev else min(den-num, 3*num-den))
    t = num*z1 - den*z2
    s = (den+num)*z1 + (den-num)*z2
    return (a - T <= t <= den + num - a) and (l <= s <= mu*T + 2*num - l)

def add(*vs):
    return (sum(v[0] for v in vs), sum(v[1] for v in vs))
def sub(a, b): return (a[0]-b[0], a[1]-b[1])

def sources(d, n, e, r, flag):
    # P=(d,n) odd, Q=(e,r) even as (den,num)
    VP = (n-d, n+d); VQ = (r-e, r+e); QQ = (e, r); PP = (2*d, 2*n)
    if flag:  # delta = -1
        return [('Q', (0,0)) if False else ('P', (0,0)), ('P', VP), ('P', add(QQ, VQ)), ('P', add(QQ, VQ, VP)),
                ('Q', PP), ('Q', add(VP, VP))]
    else:     # delta = +1
        return [('Q', (0,0)), ('Q', add(PP, VP, VP)), ('P', QQ), ('P', add(QQ, VP)), ('P', VQ), ('P', add(VQ, VP))]

def member(d, n, e, r, src, z):
    kind, v = src
    if kind == 'P':
        return inH_P(d, n, sub(z, v))
    return inH_Q(e, r, sub(z, v))

def inH_P(d, n, w): return inH(n, d, w)
def inH_Q(e, r, w): return inH(r, e, w)

def cell_uv(D, N, z):
    # cell of X with den D, num N (mu=1): U=(D,N), V=(N-D, D+N)
    U = (D, N); V = (N-D, D+N)
    # z1 - 1/2 = u U1 + v V1 ; z2 + 1/2 = u U2 + v V2
    a11, a12 = F(U[0]), F(V[0]); a21, a22 = F(U[1]), F(V[1])
    b1 = F(2*z[0]-1, 2); b2 = F(2*z[1]+1, 2)
    det = a11*a22 - a12*a21
    u = (b1*a22 - a12*b2)/det
    v = (a11*b2 - a21*b1)/det
    return u, v

def cell_points(D, N):
    U = (D, N); V = (N-D, D+N)
    pts = []
    # bounding box of the parallelogram: corners B0 + {0,U,V,U+V}, B0=(1/2,-1/2)
    xs = [0, U[0], V[0], U[0]+V[0]]; ys = [0, U[1], V[1], U[1]+V[1]]
    for z1 in range(min(xs)-1, max(xs)+3):
        for z2 in range(min(ys)-2, max(ys)+3):
            u, v = cell_uv(D, N, (z1, z2))
            if 0 <= u < 1 and 0 <= v < 1:
                pts.append(((z1, z2), u, v))
    return pts

def check_pair(d, n, e, r, flag):
    D = 2*d + e; N = 2*n + r
    srcs = sources(d, n, e, r, flag)
    bad = []
    cnt = 0
    for z, u, v in cell_points(D, N):
        cnt += 1
        if not any(member(d, n, e, r, s, z) for s in srcs):
            bad.append((z, u, v))
    return cnt, bad

if __name__ == '__main__':
    maxden = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    tot = 0; fails = 0
    for d in range(2, maxden+1):
        for n in range(1, d):
            if (d+n) % 2 != 1 or gcd(d, n) != 1: continue
            for e in range(2, maxden+1):
                for r in range(1, e):
                    if (e+r) % 2 != 0 or gcd(e, r) != 1: continue
                    dt = d*r - n*e
                    if dt not in (1, -1): continue
                    flag = (dt == 1)  # placeholder: decided below
                    for fl in (True, False):
                        # flag true <-> delta = -1 (matches odd child convention)
                        if (dt == -1) != fl: continue
                        cnt, bad = check_pair(d, n, e, r, fl)
                        tot += 1
                        if bad:
                            fails += 1
                            if fails <= 8: print('FAIL', (d,n,e,r), 'flag', fl, 'delta', dt, bad[:3])
    print('pairs', tot, 'fails', fails)
