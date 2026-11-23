import sympy as sp
from sym_all import d, n, e, r
from gen_fam import L, site_ops, MIN

def sym_parts(m, delta, f, parity, branch):
    """Sympy and Lean-string data for one (family, parity, branch)."""
    op, oq = site_ops(m, delta)
    orig = op if f == 'P' else oq
    vt = orig[MIN[(m, delta, f, 't')]]; vs = orig[MIN[(m, delta, f, 's')]]
    Nc, Dc = m*n + r, m*d + e
    TCs = Dc**2 + 2*Dc*Nc - Nc**2
    g0t = sp.expand(Nc*vt[0] - Dc*vt[1])
    g0s = sp.expand((Dc+Nc)*vs[0] + (Dc-Nc)*vs[1])
    K = (d+n)*e + (d-n)*r
    if f == 'P':
        Dn = d**2 + 2*d*n - n**2; pn, pd, mu = n, d, 2; Lf = d + n
        pn_s, pd_s = 'n', 'd'; Dn_s = '(d ^ 2 + 2 * d * n - n ^ 2)'
        aP_val = {'below': (2*n, '2 * n'), 'above': (d-n, '(d - n)')}
        aQ_val = {'below': (2*r, '2 * r'), 'above': (e-r, '(e - r)')}
        lP_o = {'below': (3*n-d, '(3 * n - d)'), 'above': (d-n, '(d - n)')}
        lQ_o = {'below': (3*r-e, '(3 * r - e)'), 'above': (e-r, '(e - r)')}
    else:
        Dn = e**2 + 2*e*r - r**2; pn, pd, mu = r, e, 1; Lf = e + r
        pn_s, pd_s = 'r', 'e'; Dn_s = '(e ^ 2 + 2 * e * r - r ^ 2)'
        aP_val = {'below': (2*n, '2 * n'), 'above': (d-n, '(d - n)')}
        aQ_val = {'below': (2*r, '2 * r'), 'above': (e-r, '(e - r)')}
        lP_o = {'below': (3*n-d, '(3 * n - d)'), 'above': (d-n, '(d - n)')}
        lQ_o = {'below': (3*r-e, '(3 * r - e)'), 'above': (e-r, '(e - r)')}
    M = e + r
    # the parent's own a/l at this parity (F = the family's parent)
    if parity == 'even':
        aF = aP_val[branch] if f == 'P' else aQ_val[branch]
        lF = (sp.Integer(0), '0')
    else:
        aF = (n, 'n') if f == 'P' else (r, 'r')
        lF = lP_o[branch] if f == 'P' else lQ_o[branch]
    # the child's a and l at this parity
    if parity == 'even':
        aC = (m*aP_val[branch][0] + aQ_val[branch][0], f"{m} * ({aP_val[branch][1]}) + ({aQ_val[branch][1]})")
        lC = (sp.Integer(0), '0')
    else:
        aC = (m*n + r, f"{m} * n + r")
        lC = (m*lP_o[branch][0] + lQ_o[branch][0], f"{m} * ({lP_o[branch][1]}) + ({lQ_o[branch][1]})")
    TC_s = f"(({m} * d + e) ^ 2 + 2 * ({m} * d + e) * ({m} * n + r) - ({m} * n + r) ^ 2)"
    g0t_s = f"(({m} * n + r) * ({L(vt[0])}) - ({m} * d + e) * ({L(vt[1])}))"
    g0s_s = f"((({m} * d + e) + ({m} * n + r)) * ({L(vs[0])}) + (({m} * d + e) - ({m} * n + r)) * ({L(vs[1])}))"
    return dict(Dn=Dn, Dn_s=Dn_s, K=K, K_s='((d + n) * e + (d - n) * r)', pn=pn, pd=pd, mu=mu, Lf=Lf,
                pn_s=pn_s, pd_s=pd_s, aF=aF, lF=lF, aC=aC, lC=lC, TCs=TCs, TC_s=TC_s,
                g0t=sp.expand(g0t), g0s=sp.expand(g0s), g0t_s=g0t_s, g0s_s=g0s_s, vt=vt, vs=vs,
                vt_s=f"({L(vt[0])}, {L(vt[1])})", vs_s=f"({L(vs[0])}, {L(vs[1])})")

def margin_sym(m, delta, f, facet, sp_):
    Dn, K = sp_['Dn'], sp_['K']; aF = sp_['aF'][0]; lF = sp_['lF'][0]
    aC = sp_['aC'][0]; lC = sp_['lC'][0]; TC = sp_['TCs']; Lf = sp_['Lf']; pn = sp_['pn']; mu = sp_['mu']
    k = 1 if (facet == 't' and m == 1) else 2
    if facet == 't':
        g0 = sp_['g0t']
        if f == 'P':
            corner = (m*Dn + K)*(aF - Dn) + (lF if delta == 1 else -(mu*Dn + 2*pn - lF))
        else:
            corner = (Dn + m*K)*(aF - Dn) + (-m*(Dn + 2*pn - lF) if delta == 1 else m*lF)
        return sp.expand(Dn*(g0 - aC + TC) + corner + k*Dn), k
    else:
        g0 = sp_['g0s']
        if f == 'P':
            corner = (m*Dn + K)*lF + (2*(aF - Dn) if delta == 1 else -2*(Lf - aF))
        else:
            corner = (Dn + m*K)*lF + (-2*m*(Lf - aF) if delta == 1 else 2*m*(aF - Dn))
        return sp.expand(Dn*(g0 - lC) + corner + k*Dn), k

def qr(Mexpr, delta):
    h = sp.expand(d*r - n*e - delta)
    qs, R = sp.reduced(Mexpr, [h], d, r, n, e, order='lex')
    return sp.expand(qs[0]), sp.expand(R)

if __name__ == "__main__":
    import itertools
    for m, delta, f, facet, parity, branch in itertools.product((1,2),(1,-1),('P','Q'),('t','s'),('even','odd'),('below','above')):
        s_ = sym_parts(m, delta, f, parity, branch)
        Mx, k = margin_sym(m, delta, f, facet, s_)
        q, R = qr(Mx, delta)
        print(m, delta, f, facet, parity, branch, 'k', k, 'R =', sp.factor(R))
