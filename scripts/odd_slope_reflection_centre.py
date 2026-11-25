"""The reflected check of the odd alternate target (continued from odd_slope_reflection.py).

For the frame of u = swap w with child (n, d) and centre C = (mu d + (n - d) + 1, mu n + (n + d) - 1), mu = 1 if n + d even else 2:
1. the standard field has the reflection F(C - y) = F(y) - t(y) + kappa with t(y) = n y1 - d y2 (checked numerically, all sites);
2. hence H_+(C - p) = H_-(p) + L(p) - (1/2) grad L . sigma with L = -t + const (the identity under test);
3. the alternate target alt(z) = Q_+(z - T) + J . z is then Q_-(x') + affine(z), where x' = Z^{-1}(C - Z(z - T)), Z(x') = C - Z(z - T).

This script computes the residual R(z) = alt(z) - Q_-(x'(z)) on the copy sites and checks whether it is affine (constant after subtracting a
gradient), and reports that gradient, to compare with the odd parent slope J = (N, -D) and with grad L = (-n, d).
"""
import odd_slope_reflection as osr
from odd_copy_check import copy as ODD
from seventh_jet import parents_of, phase
from alt_jets import lexmin
from odd_copy_candidates import Z, h, sub, add
from odd_seventh_check import raw_target

standard, Frame, swap = osr.standard, osr.Frame, osr.swap


def centre(fr):
    n, d = fr.n, fr.d
    mu = 1 if (n + d) % 2 == 0 else 2
    return (mu * d + (n - d) + 1, mu * n + (n + d) - 1)


def reflection_residual_constant(u):
    F = standard(u)[0]
    fr = Frame(list(u))
    C = centre(fr)
    n, d = fr.n, fr.d
    vals = set()
    for y1 in range(-6, 7):
        for y2 in range(-6, 7):
            y = (y1, y2)
            vals.add(F(sub(C, y)) - F(y) + (n * y1 - d * y2))
    return len(vals), sorted(vals)[:5], C, (n, d)


def check(w):
    u = tuple(swap(list(w)))
    F = standard(u)[0]
    fr = Frame(list(u))
    sigma = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    C = centre(fr)
    (N, D), (nq, dq) = parents_of(w)
    ph = phase(w)
    J = (N, -D) if ph == 1 else (0, 0)
    delta = (N - D - dq, N + D - nq) if ph == 1 else (0, 0)
    sites = [s for (tag, lst) in ODD[w].items() for (s, _) in lst]
    LL = lexmin(sites)
    T = (delta[0] - LL[0], delta[1] - LL[1])
    raw = raw_target(w)

    def alt(z):
        return raw(add(z, LL)) - (J[0] * LL[0] + J[1] * LL[1])

    def Hm(p):
        return (F(p) + F(sub(p, sigma)) + 1) // 2

    def Qm_at_reflection(x):
        p = Z(x)
        pp = sub(C, p)  # C - Z(x)
        xp = (pp[1] + 1, -pp[0])  # Z(xp) = pp
        return Hm(pp) + h(xp)

    zs = [sub(s, LL) for s in sites]

    def R(z):
        return alt(z) - Qm_at_reflection(sub(z, T))

    z0 = zs[0]
    g1 = (R(add(z0, (1, 0))) - R(z0), R(add(z0, (0, 1))) - R(z0))
    resid = set()
    for z in zs:
        resid.add(R(z) - g1[0] * (z[0] - z0[0]) - g1[1] * (z[1] - z0[1]) - R(z0))
    return len(resid), g1, J, (-fr.n, fr.d), C


if __name__ == "__main__":
    words = sorted([w for w in ODD if w and w[-1] in (1, 3) and not all(d == 3 for d in w)], key=lambda t: (len(t), t))
    u0 = tuple(swap([1]))
    print("symmetry of F about the centre, distinct values over a window (1 = exact):",
          reflection_residual_constant(u0)[:2], flush=True)
    summary = {}
    for w in words:
        k, g1, J, gL, C = check(w)
        ph = phase(w)
        summary.setdefault(ph, []).append((w, k))
        print(w, "phase", ph, "affine-residual distinct values", k, "gradient", g1, "J", J, "grad L", gL, "C", C, flush=True)
    for ph in sorted(summary):
        ones = sum(1 for (w, k) in summary[ph] if k == 1)
        print("phase", ph, "affine (constant residual after gradient) on", ones, "of", len(summary[ph]))
