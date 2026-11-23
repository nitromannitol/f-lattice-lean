import sympy as sp
from sym_all import d, n, e, r
from gen_fam import L, site_ops, MIN

def C_of(m):
    return m*n + r, m*d + e          # (num, den) of the child

def mu_of(num, den):
    return 2 if (num + den) % 2 == 1 else 1   # for symbolic parity we pass known types

def refl_const(f, m, delta):
    """refl X 0 = (muD + N - D + 1, muN + D + N - 1) for X=(D,N) site-type (num=N, den=D)."""
    if f == 'P': N, D, mu = n, d, 2
    elif f == 'Q': N, D, mu = r, e, 1
    else: Nc, Dc = C_of(m); N, D, mu = Nc, Dc, (2 if m == 1 else 1)
    return (sp.expand(mu*D + N - D + 1), sp.expand(mu*N + D + N - 1))

def refl_child(m):
    Nc, Dc = C_of(m)
    mu = 2 if m == 1 else 1
    return (sp.expand(mu*Dc + Nc - Dc + 1), sp.expand(mu*Nc + Dc + Nc - 1))

def reflected_origin(m, delta, f, v):
    RC = refl_child(m)
    Rf = refl_const(f, m, delta)
    return (sp.expand(RC[0] - Rf[0] - v[0]), sp.expand(RC[1] - Rf[1] - v[1]))

def grade(m, v, facet):
    Nc, Dc = C_of(m)
    if facet == 't': return sp.expand(Nc*v[0] - Dc*v[1])
    return sp.expand((Dc + Nc)*v[0] + (Dc - Nc)*v[1])

if __name__ == "__main__":
    for m, delta in [(1,1),(1,-1),(2,1),(2,-1)]:
        op, oq = site_ops(m, delta)
        for f, orig in (('P', op), ('Q', oq)):
            table = [tuple(sp.expand(c) for c in v) for v in orig]
            for j, v in enumerate(orig):
                vr = reflected_origin(m, delta, f, v)
                vr = tuple(sp.expand(c) for c in vr)
                inside = [i for i, t in enumerate(table) if sp.simplify(t[0]-vr[0]) == 0 and sp.simplify(t[1]-vr[1]) == 0]
                print(m, delta, f, 'origin', j, 'reflected', vr, 'in table at', inside)
