"""Paragraph 5, the field identity (provisional): with f = Fp = quarterTurnField(G) =
pl.standard(w) (the field used by sheetA, sheetA(z) = Fp(z - (1-W) U_q)), and the conjugate field G = pl.standard(u),
u = swap(odd_birth_prefix(w)):
  A1(x) = f(x - eps U_q) - f(x),      U_q = (d_q, n_q) = the even parent's kernel of w (word's own even parent);
  A2(x) = f(x + delta0) - f(x),       delta0 = (-eps_c (N_c+D_c), eps_c (N_c-D_c)) from the CONJUGATE's odd parent
                                       (the shift of quarterTurnField_sub_shift);
  R(x)  = c0 - P(Zx),  P = conj.price G, c0 = conj.cutPrice, Z x = (-x2, x1-1).
Sanity: A2 == R must hold (it is the codebase identity F(x) - F(x+delta0) = P(Zx) - c0 read backwards).
Domain: z in the window box of w's frame, x = z - l_v with l_v = (1-W) U_q (the paragraph's x = z - l_v).
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    if all(x == 3 for x in w):
        return {"cube skipped": 1}, None
    u = list(pl.swap(pl.odd_birth_prefix(w)))
    out = defaultdict(int)
    if not u:
        out["conjugate empty, skipped"] += 1
        return out, None
    G, _ = pl.standard(tuple(u))
    F = lambda x: G((-x[1], x[0] - 1)) + pl.h0(*x)  # f = Fp = quarterTurnField(G), the field sheetA uses
    fr = oc.frame(w)
    N, D, nq, dq, eps = fr["N"], fr["D"], fr["nq"], fr["dq"], fr["eps"]
    fc = oc.frame(u)
    Nc, Dc, epsc = fc["N"], fc["D"], fc["eps"]
    Tpc = Dc * Dc + 2 * Dc * Nc - Nc * Nc
    c0 = (Tpc - epsc * (Dc + Nc)) // 2
    ps = (epsc * (Nc - Dc), epsc * (Nc + Dc))

    def P(z):
        return G(z) - G((z[0] - ps[0], z[1] - ps[1])) - epsc * (Nc * z[0] - Dc * z[1])

    Z = lambda x: (-x[1], x[0] - 1)
    delta0 = (-epsc * (Nc + Dc), epsc * (Nc - Dc))
    W = (1 + eps) // 2
    lv = ((1 - W) * dq, (1 - W) * nq)
    epsUq = (eps * dq, eps * nq)
    x0, x1, y0, y1 = oc.window(fr)
    for zy in range(y0, y1 + 1):
        for zx in range(x0, x1 + 1):
            z = (zx, zy)
            x = (z[0] - lv[0], z[1] - lv[1])
            base = F(x)
            A1 = F((x[0] - epsUq[0], x[1] - epsUq[1])) - base
            A2 = F((x[0] + delta0[0], x[1] + delta0[1])) - base
            R = c0 - P(Z(x))
            out[("A2 == R (codebase sanity)", A2 == R)] += 1
            out[("A1 == R (paper's eps U_q)", A1 == R)] += 1
            out[("A1 == A2 (bridge)", A1 == A2)] += 1
            if A1 != A2 and out["ex"] == 0:
                out["ex"] = 1
                ex = (tuple(w), z, x, (A1, A2, R), (dq, nq), (N, D), eps, delta0, epsUq)
            else:
                ex = None
    out["ex"] = 0
    return out, ex


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    exs = []
    with Pool(12) as pool:
        for out, ex in pool.imap_unordered(run, ws):
            for k, v in out.items():
                if k == "ex":
                    continue
                tot[k] += v
            if ex is not None:
                exs.append(ex)
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
    exs.sort(key=lambda e: (len(e[0]), e[0]))
    print("smallest A1 != A2:", exs[:1], flush=True)
