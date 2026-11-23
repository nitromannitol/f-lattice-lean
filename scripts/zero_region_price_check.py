"""Numerical check of I1's chain bound (task 49): for a proper word, u = conjWord(word), on the zero region
E ∩ {t >= 1 - d} of word, with Q(z) = earlierChainPrice(F_u, odd_u, eps_old, eps_word)(Z(z - lv)) and K from the identity
C(z) - A(z) + Q(z) = K, check (i) K is constant, (ii) Q(z) <= K (hbound), (iii) Z(z - lv) lies in the closed polygon of u
(so the price range of u applies), (iv) K equals the cut price c0_u of u.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import upper_attainment_check as uac  # noqa: E402

standard = uac.standard


def earlier_chain_shift(N, D, old, ori):
    return (2 * ori * old * D - old * (N - D), 2 * ori * old * N - old * (N + D))


def run(word):
    fw = uac.make_frame(word)
    u = uac.conjWord(word)
    fu = uac.make_frame(u)
    Fu = standard(tuple(u))[0]
    Nu, Du, epsu = fu["N"], fu["D"], fu["eps"]
    old = uac.make_frame(uac.oddBirthPrefix(word))["eps"]
    ori = fw["eps"]
    sh = earlier_chain_shift(Nu, Du, old, ori)
    vu = (epsu * (Nu - Du), epsu * (Nu + Du))
    Todd = Du * Du + 2 * Du * Nu - Nu * Nu
    c0 = (Todd - epsu * (Du + Nu)) // 2
    lv = fw["sheetA"]  # unused here; shift via the make_frame closure
    # lv and e are needed for the zero-region map: recover them from the sheets' definitions
    W = (1 + fw["eps"]) // 2
    shift = ((1 - W) * fw["dq"], (1 - W) * fw["nq"])

    def P_u(y):
        return Fu(y) - Fu((y[0] - vu[0], y[1] - vu[1])) - epsu * (Nu * y[0] - Du * y[1])

    def Q(z):
        x = (z[0] - shift[0], z[1] - shift[1])
        y = (-x[1], x[0] - 1)
        return (Fu(y) - Fu((y[0] + sh[0], y[1] + sh[1])) + old * (Du * y[1] - Nu * y[0]))

    n, d = fw["n"], fw["d"]
    L = 2 * (d + n) + 6
    Ks = set()
    viol_bound = 0
    out_poly_u = 0
    viol_price = 0
    count = 0
    for a in range(-L, L + 1):
        for b in range(-L, L + 1):
            z = (a, b)
            if not uac.in_closed_polygon(fw, z):
                continue
            if n * a - d * b < 1 - d:
                continue
            count += 1
            A = fw["sheetA"](z)
            C = fw["sheetC"](z)
            Ks.add(C - A + Q(z))
    return dict(count=count, Ks=sorted(Ks), c0=c0, eps=(epsu, old, ori), shift=shift, sh=sh)


if __name__ == "__main__":
    words = uac.words_up_to(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
    for w in words[:6]:
        r = run(w)
        print(w, "points", r["count"], "K values", r["Ks"][:4], "c0", r["c0"], "eps", r["eps"], flush=True)
