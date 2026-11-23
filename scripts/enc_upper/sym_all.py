import sympy as sp, itertools, random
from enc_num import pairs
d,n,e,r = sp.symbols('d n e r', integer=True)

def origins(m, delta):
    Pv = (d, n); Qv = (e, r)
    vP = (n-d, d+n); vQ = (r-e, e+r)
    add = lambda *vs: (sum(v[0] for v in vs), sum(v[1] for v in vs))
    mul = lambda k, v: (k*v[0], k*v[1])
    if m == 2 and delta == 1:
        Oq = [(0,0), add(mul(2,Pv), mul(2,vP))]
        Op = [Qv, add(Qv, vP), vQ, add(vQ, vP)]
    elif m == 2 and delta == -1:
        Oq = [mul(2,Pv), mul(2,vP)]
        Op = [(0,0), vP, add(Qv, vQ), add(Qv, vQ, vP)]
    elif m == 1 and delta == 1:
        Oq = [(0,0), Qv, add(mul(2,Pv), vP), add(mul(2,Pv), vP, Qv)]
        Op = [mul(2,Qv), vQ]
    else:
        Oq = [mul(2,Pv), add(mul(2,Pv), Qv), vP, add(vP, Qv)]
        Op = [(0,0), add(mul(2,Qv), vQ)]
    return Op, Oq

def grades(m, delta, Nc, Dc):
    pass

# numeric sampler of pairs to find the minimizing origin, identical across pairs
def min_origin_names(m, delta, f, facet):
    Op, Oq = origins(m, delta)
    orig = Op if f == 'P' else Oq
    names = None
    res = {}
    for (P, Q, flag) in pairs(12):
        nn, dd = P; rr, ee = Q
        if (dd*rr - nn*ee) != delta: continue
        Nc, Dc = m*nn + rr, m*dd + ee
        subs = {d: dd, n: nn, e: ee, r: rr}
        vals = []
        for i, o in enumerate(orig):
            ox, oy = int(sp.sympify(o[0]).subs(subs)), int(sp.sympify(o[1]).subs(subs))
            if facet == 't': vals.append(Nc*ox - Dc*oy)
            else: vals.append((Dc+Nc)*ox + (Dc-Nc)*oy)
        j = min(range(len(vals)), key=lambda i: vals[i])
        res.setdefault(j, 0); res[j] += 1
    return res

if __name__ == "__main__":
    for m, delta, f, facet in itertools.product((1,2), (1,-1), ('P','Q'), ('t','s')):
        print(m, delta, f, facet, "min-origin index histogram:", min_origin_names(m, delta, f, facet))
