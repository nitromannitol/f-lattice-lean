import sys
from math import gcd

def mu(num, den):  return 2 if (num + den) % 2 == 1 else 1
def T(num, den):   return den*den + 2*den*num - num*num
def a_of(num, den, ev): return min(2*num, den-num) if ev else num
def l_of(num, den, ev): return 0 if ev else min(den-num, 3*num-den)

def inH(f, z):
    num, den = f
    z1, z2 = z
    ev = (z1+z2) % 2 == 0
    a = a_of(num, den, ev); l = l_of(num, den, ev)
    t = num*z1 - den*z2
    s = (den+num)*z1 + (den-num)*z2
    Tf = T(num, den); m = mu(num, den)
    return (a - Tf <= t <= den+num-a) and (l <= s <= m*Tf + 2*num - l)

def H_points(f):
    num, den = f
    Tf = T(num, den); m = mu(num, den)
    pts = []
    for t in range(-Tf-2*den-2, den+num+Tf+2):
        for s in range(-2*Tf-4*den-4, m*Tf+2*num+4):
            # invert: w1 = ((den-num) t + den s)/T ; w2 = (-(den+num) t + num s)/T
            x = (den-num)*t + den*s
            y = -(den+num)*t + num*s
            if x % Tf == 0 and y % Tf == 0:
                z = (x//Tf, y//Tf)
                if inH(f, z):
                    pts.append(z)
    return pts

def add(a, b): return (a[0]+b[0], a[1]+b[1])
def texV1Odd(p): return (2*p[1], 2*p[0])   # (2 den, 2 num)
def texV1Even(q): return (q[1], q[0])      # (den, num)
def texV2(f): return (f[0]-f[1], f[0]+f[1])
def sc(v, k): return (k*v[0], k*v[1])

def odd_sources(flag, P, Q):
    # returns list of (name, which, shift): which 'T1'=H_P, 'T2'=H_Q
    V1o, V1e, V2p, V2q = texV1Odd(P), texV1Even(Q), texV2(P), texV2(Q)
    if flag:
        return [("T2@V1o", 'T2', V1o), ("T2@V1o+V1e", 'T2', add(V1o, V1e)),
                ("T2@V2p", 'T2', V2p), ("T2@V2p+V1e", 'T2', add(V2p, V1e)),
                ("T1@0", 'T1', (0, 0)), ("T1@2V1e+V2q", 'T1', add(add(V1e, V1e), V2q))]
    else:
        return [("T2@0", 'T2', (0, 0)), ("T2@V1e", 'T2', V1e), ("T2@V1o+V2p", 'T2', add(V1o, V2p)),
                ("T2@V1o+V2p+V1e", 'T2', add(add(V1o, V2p), V1e)), ("T1@2V1e", 'T1', add(V1e, V1e)),
                ("T1@V2q", 'T1', V2q)]

def even_sources(flag, P, Q):
    V1o, V1e, V2p, V2q = texV1Odd(P), texV1Even(Q), texV2(P), texV2(Q)
    if flag:
        return [("T2@V1o", 'T2', V1o), ("T2@2V2p", 'T2', add(V2p, V2p)), ("T1@0", 'T1', (0, 0)),
                ("T1@V2p", 'T1', V2p), ("T1@V1e+V2q", 'T1', add(V1e, V2q)),
                ("T1@V1e+V2q+V2p", 'T1', add(add(V1e, V2q), V2p))]
    else:
        return [("T2@0", 'T2', (0, 0)), ("T2@V1o+2V2p", 'T2', add(V1o, add(V2p, V2p))),
                ("T1@V1e", 'T1', V1e), ("T1@V1e+V2p", 'T1', add(V1e, V2p)),
                ("T1@V2q", 'T1', V2q), ("T1@V2q+V2p", 'T1', add(V2q, V2p))]

def pairs(D):
    out = []
    for d in range(2, D+1):
        for n in range(1, d):
            if (d+n) % 2 != 1: continue
            for e in range(2, D+1):
                for r in range(1, e):
                    if (e+r) % 2 != 0: continue
                    det = n*e - r*d
                    if det in (1, -1):
                        out.append(((n, d), (r, e), det == 1))
    return out

if __name__ == "__main__":
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    P_ps = pairs(D)
    print("proper pairs:", len(P_ps))
    fails = {}
    npts = 0
    for (P, Q, flag) in P_ps:
        HP = H_points(P); HQ = H_points(Q)
        npts += len(HP) + len(HQ)
        Xo = (P[0]+Q[0], P[1]+Q[1]); Xe = (2*P[0]+Q[0], 2*P[1]+Q[1])
        for kind, X, srcs in (("odd", Xo, odd_sources), ("even", Xe, even_sources)):
            for (name, which, v) in srcs(flag, P, Q)[0:6]:
                S = HQ if which == 'T2' else HP
                for w in S:
                    z = add(w, v)
                    if not inH(X, z):
                        key = (kind, flag, name)
                        fails.setdefault(key, []).append((P, Q, w, z))
    print("points checked:", npts)
    if not fails:
        print("ALL CONTAINMENTS HOLD")
    for k, v in sorted(fails.items()):
        print(k, len(v), v[:2])
