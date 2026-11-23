import sympy as sp
from sym_all import d, n, e, r

def L(x):  # sympy -> lean text
    return str(sp.expand(x)).replace('**', '^')

def site_ops(m, delta):
    Pv = (d, n); Qv = (e, r); vP = (n-d, n+d); vQ = (r-e, r+e)
    add = lambda *vs: (sum(v[0] for v in vs), sum(v[1] for v in vs))
    mul = lambda k, v: (k*v[0], k*v[1])
    if m == 1 and delta == 1:
        Oq = [(0,0), Qv, add(mul(2,Pv), vP), add(mul(2,Pv), vP, Qv)]; Op = [mul(2,Qv), vQ]
    elif m == 1 and delta == -1:
        Oq = [mul(2,Pv), add(mul(2,Pv), Qv), vP, add(vP, Qv)]; Op = [(0,0), add(mul(2,Qv), vQ)]
    elif m == 2 and delta == 1:
        Oq = [(0,0), add(mul(2,Pv), mul(2,vP))]; Op = [Qv, add(Qv, vP), vQ, add(vQ, vP)]
    else:
        Oq = [mul(2,Pv), mul(2,vP)]; Op = [(0,0), vP, add(Qv, vQ), add(Qv, vQ, vP)]
    return Op, Oq

MIN = {(1,1,'P','t'):1, (1,1,'P','s'):1, (1,1,'Q','t'):3, (1,1,'Q','s'):0,
       (1,-1,'P','t'):1, (1,-1,'P','s'):0, (1,-1,'Q','t'):2, (1,-1,'Q','s'):2,
       (2,1,'P','t'):3, (2,1,'P','s'):3, (2,1,'Q','t'):1, (2,1,'Q','s'):0,
       (2,-1,'P','t'):3, (2,-1,'P','s'):0, (2,-1,'Q','t'):1, (2,-1,'Q','s'):1}

def lean_site(v):
    return f"({L(v[0])}, {L(v[1])})"

def build_family(m, delta, f):
    Op, Oq = site_ops(m, delta)
    orig = Op if f == 'P' else Oq
    vt = orig[MIN[(m, delta, f, 't')]]; vs = orig[MIN[(m, delta, f, 's')]]
    if f == 'P':
        pn, pd, Dn, mu = n, d, d**2 + 2*d*n - n**2, 2
        pn_s, pd_s, Dn_s = 'n', 'd', '(d ^ 2 + 2 * d * n - n ^ 2)'
        Lf = d + n
        aF_e = {'below': ('2 * n', 'lfe'), 'above': ('(d - n)', 'lfe')}
        aF_o = 'n'
        lF_o = {'below': '(3 * n - d)', 'above': '(d - n)'}
        aQ_e = {'below': '2 * r', 'above': '(e - r)'}
        aQ_o = 'r'; lQ_o = {'below': '(3 * r - e)', 'above': '(e - r)'}
        aP_e = {'below': '2 * n', 'above': '(d - n)'}
        Sym_aP_e, Sym_aQ_e = {'below': 2*n, 'above': d-n}, {'below': 2*r, 'above': e-r}
        Sym_lP_o, Sym_lQ_o = {'below': 3*n-d, 'above': d-n}, {'below': 3*r-e, 'above': e-r}
        Sym_aP_o, Sym_aQ_o = n, r
        Sym_Dn = d**2 + 2*d*n - n**2
        Sym_Lf = d + n
        Sym_pn, Sym_pd = n, d
    else:
        Dn_s = '(e ^ 2 + 2 * e * r - r ^ 2)'
        Sym_Dn = e**2 + 2*e*r - r**2
        Sym_Lf = e + r
        Sym_aP_e, Sym_aQ_e = {'below': 2*n, 'above': d-n}, {'below': 2*r, 'above': e-r}
        Sym_lP_o, Sym_lQ_o = {'below': 3*n-d, 'above': d-n}, {'below': 3*r-e, 'above': e-r}
        Sym_aP_o, Sym_aQ_o = n, r
        Sym_pn, Sym_pd = r, e
    return dict(m=m, delta=delta, f=f, orig=orig, vt=vt, vs=vs, Dn_s=Dn_s, Sym_Dn=Sym_Dn,
                Sym_Lf=Sym_Lf, Sym_pn=Sym_pn, Sym_pd=Sym_pd, Sym_aP_e=Sym_aP_e, Sym_aQ_e=Sym_aQ_e,
                Sym_lP_o=Sym_lP_o, Sym_lQ_o=Sym_lQ_o)
