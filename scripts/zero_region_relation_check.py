"""For proper words: relate Q(z) = earlierChainPrice(...)(Z(z - lv)) to the price P_u of u, test whether Z(z - lv) lies in
the closed polygon of u, and test hbound Q(z) <= K on the zero region (K the identity constant)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import upper_attainment_check as uac  # noqa: E402
from zero_region_price_check import earlier_chain_shift  # noqa: E402

standard = uac.standard


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
    W = (1 + fw["eps"]) // 2
    shift = ((1 - W) * fw["dq"], (1 - W) * fw["nq"])
    Todd = Du * Du + 2 * Du * Nu - Nu * Nu
    c0 = (Todd - epsu * (Du + Nu)) // 2

    def P_u(y):
        return Fu(y) - Fu((y[0] - vu[0], y[1] - vu[1])) - epsu * (Nu * y[0] - Du * y[1])

    def Zmap(z):
        x = (z[0] - shift[0], z[1] - shift[1])
        return (-x[1], x[0] - 1)

    def Q(z):
        y = Zmap(z)
        return Fu(y) - Fu((y[0] + sh[0], y[1] + sh[1])) + old * (Du * y[1] - Nu * y[0])

    n, d = fw["n"], fw["d"]
    L = 2 * (d + n) + 6
    K = None
    diffs = set()
    in_poly = 0
    total = 0
    qmax_minus_K = None
    Qvals = []
    Pvals = []
    for a in range(-L, L + 1):
        for b in range(-L, L + 1):
            z = (a, b)
            if not uac.in_closed_polygon(fw, z) or n * a - d * b < 1 - d:
                continue
            total += 1
            Kz = fw["sheetC"](z) - fw["sheetA"](z) + Q(z)
            K = Kz if K is None else K
            y = Zmap(z)
            diffs.add(Q(z) - P_u(y))
            if uac.in_closed_polygon(fu, y):
                in_poly += 1
                Pvals.append(P_u(y))
            Qvals.append(Q(z))
    return dict(total=total, K=K, c0=c0, diffs=sorted(diffs)[:6], in_poly=in_poly,
                qmax=max(Qvals) if Qvals else None, pmax=max(Pvals) if Pvals else None,
                pmin=min(Pvals) if Pvals else None)


if __name__ == "__main__":
    words = [w for w in uac.words_up_to(2) if any(x != 3 for x in w)]
    for w in words:
        r = run(w)
        print(w, "zero pts", r["total"], "K", r["K"], "c0", r["c0"], "Q-P_u diffs", r["diffs"],
              "in poly_u", r["in_poly"], "Qmax", r["qmax"], "P_u range on poly", (r["pmin"], r["pmax"]), flush=True)
