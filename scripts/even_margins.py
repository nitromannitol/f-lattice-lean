import sys
from fractions import Fraction as F
from math import gcd
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from even_agg import pairs

def wparams(num, den):
    mu = 2 if (num + den) % 2 == 1 else 1
    T = den*den + 2*den*num - num*num
    return mu, T

def a_l(num, den, ev):
    a = min(2*num, den-num) if ev else num
    l = 0 if ev else min(den-num, 3*num-den)
    return a, l

def cell_corner(D, N, u, v):
    U = (D, N); V = (N-D, D+N)
    z1 = F(1, 2) + u*U[0] + v*V[0]
    z2 = F(-1, 2) + u*U[1] + v*V[1]
    return z1, z2

def margins(num, den, s, z1, z2, ev):
    """real margins for w = z - s, with parity class ev (a,l taken at that parity)."""
    w1 = z1 - s[0]; w2 = z2 - s[1]
    mu, T = wparams(num, den)
    a, l = a_l(num, den, ev)
    t = num*w1 - den*w2
    sc = (den+num)*w1 + (den-num)*w2
    return {
        'tlo': t - (a - T),            # need > -1
        'thi': (den+num-a) - t,        # need > -1
        'slo': sc - l,                 # need > -1
        'shi': (mu*T + 2*num - l) - sc # need > -1
    }

def box_margin_min(num, den, s, box, ev, D, N):
    u0, u1, v0, v1 = box
    res = {}
    for u in (u0, u1):
        for v in (v0, v1):
            z1, z2 = cell_corner(D, N, u, v)
            m = margins(num, den, s, z1, z2, ev)
            for k, val in m.items():
                res[k] = min(res.get(k, 10**9), val)
    return res

def pieces(d, n, e, r, al, be):
    # flag F base pieces (delta=+1): Q=(e,r) at 0 on [0,be]^2; P=(d,n) at Q on [be,1]x[0,al/2]; P at Q+VP on [be,1]x[al/2,al]
    VP = (n-d, n+d); VQ = (r-e, r+e); Q = (e, r); P2 = (2*d, 2*n)
    F_ = {
        'F1 Q@0 [0,be]^2': ((e, r), (0, 0), (0, be, 0, be)),
        'F3L P@Q [be,1]x[0,al/2]': ((d, n), Q, (be, 1, 0, al/2)),
        'F3H P@(Q+VP) [be,1]x[al/2,al]': ((d, n), (Q[0]+VP[0], Q[1]+VP[1]), (be, 1, al/2, al)),
    }
    T_ = {
        'T1 Q@2P [al,1]x[0,be]': ((e, r), P2, (al, 1, 0, be)),
        'T3L P@0 [0,al]x[0,al/2]': ((d, n), (0, 0), (0, al, 0, al/2)),
        'T3H P@VP [0,al]x[al/2,al]': ((d, n), VP, (0, al, al/2, al)),
    }
    return F_, T_

if __name__ == '__main__':
    maxden = int(sys.argv[1]); flagmode = sys.argv[2]
    worst = {}
    for (d, n, e, r, dt) in pairs(maxden):
        flag = (dt == -1)
        if (flagmode == 'T') != flag: continue
        D = 2*d + e; N = 2*n + r
        al, be = F(2*d, D), F(e, D)
        Fp, Tp = pieces(d, n, e, r, al, be)
        for name, (fr, s, box) in (list(Fp.items()) if not flag else list(Tp.items())):
            for ev in (True, False):
                # fraction is (num, den) of the source; note fr = (den, num) for P,Q
                den_f, num_f = fr
                m = box_margin_min(num_f, den_f, s, box, ev, D, N)
                for k, val in m.items():
                    key = (name, ev, k)
                    if key not in worst or val < worst[key][0]:
                        worst[key] = (val, (d, n, e, r))
    for key, (val, pr) in sorted(worst.items()):
        flagv = 'bad' if val <= -1 else 'ok'
        print(f"{key[0]:34s} ev={str(key[1]):5s} {key[2]:5s} min={float(val):8.3f} {flagv} at {pr}")
