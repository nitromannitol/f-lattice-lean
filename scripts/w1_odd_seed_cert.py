"""Task 74 (2): exact polynomial certificates for the two odd-seed identities, per eps = +-1 (W = 1 or 0).
Variables D N e r H J0 (H = (B+R)/2, J0 = (e^2+2er-r^2-e-r)/2 are the exact halves: 2H = B+R, 2 J0 = e^2+2er-r^2-e-r).
Numerators: 4 h0(x) = x1^2 + 2 x1 x2 - x2^2 - 2 x2 - parity(x).
"""
import sympy as sp

D, N, e, r, H, J0 = sp.symbols('D N e r H J0')


def num(x1, x2):
    return x1**2 + 2*x1*x2 - x2**2 - 2*x2


def run(eps):
    W = sp.Integer(1) if eps == 1 else sp.Integer(0)
    R = D + N
    b = D - N
    B = D**2 + 2*D*N - N**2
    k = (-1, -2)
    z = (R - 1 + (1 - W)*(e + r), b + 1 + (1 - W)*(e - r))
    U = (2*D + e, 2*N + r)
    Zz = (-z[1], z[0] - 1)
    Y = (Zz[0] + U[0], Zz[1] + U[1])
    tq = lambda x1, x2: r*x1 - e*x2
    tp = lambda x1, x2: N*x1 - D*x2
    v = (e + k[0], r + k[1])
    Vp = (N - D, D + N)
    Vq = (r - e, e + r)
    eps_s = sp.Integer(eps)
    y = (Vp[0] - eps_s*Vq[0] + k[0], Vp[1] - eps_s*Vq[1] + k[1])
    J = tq(Y[0] - (1 - W)*e, Y[1] - (1 - W)*r) + J0 + 2*W
    # relation: N e - D r = eps
    rel = N*e - D*r - eps_s
    relH = 2*H - B - R
    relJ = 2*J0 - (e**2 + 2*e*r - r**2 - e - r)
    # I1 : 4 h0(z) + 4 tp(v) - 4H + 4 (1-W) J   (with 4 h0(z) = num(z) since z even)
    I1 = num(*z) + 4*tp(*v) - 4*H + 4*(1 - W)*J
    # I2 : 4 h0(z) + 4 h0(y) + 4 W J   (4 h0(y) = num(y) - 1 since y odd)
    I2 = num(*z) + (num(*y) - 1) + 4*W*J
    out = {}
    for name, E in (('I1', I1), ('I2', I2)):
        E = sp.expand(E)
        gens = [rel, relH, relJ]
        qs, rem = sp.reduced(E, gens, D, N, e, r, H, J0, order='lex')
        out[name] = (sp.simplify(rem), qs)
    return out


if __name__ == '__main__':
    for eps in (1, -1):
        res = run(eps)
        for name, (rem, qs) in res.items():
            print('eps', eps, name, 'remainder', rem)
            for q, g in zip(qs, ['rel(Ne-Dr-eps)', 'relH(2H-B-R)', 'relJ(2J0-...)']):
                print('   coeff of', g, ':', sp.factor(q))
