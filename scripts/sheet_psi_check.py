"""Task 64 (a): is Psi(z) = C(z) - A(z) equal, up to sign and an additive constant, to the sheet chain
Xi(x) = Phi_eta(Z x) of the conjugate (eta = eps of the word), at z + t for a few shifts t?

Phi_eta(w) = G(w) - G(w + eta sigma' - v') - eps' (N' w1 - D' w2 - ...), with the conjugate frame (N', D', eps'),
sigma' = (2 eps' D', 2 eps' N'), v' = eps' (N' - D', N' + D'), G = standard(swap(prefix)) (= Fq), Z x = (-x2, x1 - 1).
Run as: python3 sheet_psi_check.py
"""
import itertools
import sheets as S

standard, swap, Frame = S.standard, S.swap, S.Frame


def chain(w):
    w = list(w)
    k = max(i for i, x in enumerate(w) if x in (1, 2))
    cw = tuple(swap(w[:k]))
    G = standard(cw)[0]
    fc = Frame(list(cw))
    fr = Frame(w)
    Np, Dp, ep = fc.N, fc.D, fc.eps
    eta = fr.eps
    sig = (2 * ep * Dp, 2 * ep * Np)
    v = (ep * (Np - Dp), ep * (Np + Dp))

    def Xi(x):
        wz = (-x[1], x[0] - 1)
        p = (wz[0] + eta * sig[0], wz[1] + eta * sig[1])
        Phi = G(wz) - G((p[0] - v[0], p[1] - v[1])) - ep * (Np * p[0] - Dp * p[1])
        return Phi

    return Xi, fr


def test(w, box=3):
    A, C, info = S.sheets(w)
    Xi, fr = chain(w)
    lv = info["lv"]
    res = {}
    for t_name, t in [("0", (0, 0)), ("-lv", (-lv[0], -lv[1])), ("lv", (lv[0], lv[1]))]:
        for s in (1, -1):
            vals = set()
            for z0 in range(-box, box + 1):
                for z1 in range(-box, box + 1):
                    z = (z0, z1)
                    psi = C(z) - A(z)
                    xi = Xi((z[0] + t[0], z[1] + t[1]))
                    vals.add(psi - s * xi)
            res[(t_name, s)] = len(vals) == 1
            if len(vals) == 1:
                res[(t_name, s, "const")] = vals.pop()
    return res


if __name__ == "__main__":
    words = [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1)]
    for w in words:
        r = test(w)
        print(w, {k: v for k, v in r.items()})
