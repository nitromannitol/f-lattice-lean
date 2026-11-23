"""Task 59 step 1: the Q3 facts in the odd parent's frame (N/D in its own coordinates).

Parent coordinates (W1_CONSTRUCTOR sec. 1): Lp = D+N, Tp = D^2+2DN-N^2,
  tp = N x1 - D x2,  sp = (D+N) x1 + (D-N) x2   (exact: tp = (C t + eps s)/T, sp = (C s + 2 eps t)/T).
The earlier conjugate is the frame of u = swap(odd_birth_prefix(w)) with field Fq; the field of w is
  Fp(x) = Fq(Z x) + h0(x),  Z(x) = (-x2, x1-1),  so a conjugate free site y corresponds to the parent point x = Z^{-1} y
  with Z^{-1}(y) = (y2 + 1, -y1).
Web (step one / step two): H: tp in [1, Lp-1] on even sites, [N, D] on odd sites, modulo Tp;
                           V: sp even in [0, 2N], odd in [2-D+N, Lp-2], modulo 2Tp.
Parity label: tested two ways: 'x' (EvenSite of the parent point) and 'y' (EvenSite of the conjugate free site).
Native V stars: a = J_q(y) on conjugate V sites (J = cutGrade 0 1 1); claim a in {0,1}.
Drop 1 -> 0: a prescribed kept V edge from a J=1 site to a J=0 site has its target inside the closed polygon of the
conjugate (translate index 0).
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import cut_on, words


def conj_free(u):
    fu = oc.frame(u)
    n, d = fu["n"], fu["d"]
    L = n + d
    x0, x1, y0, y1 = oc.window(fu)
    inE = lambda z: oc.in_polygon(z, fu)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    tg = lambda z: n * z[0] - d * z[1]
    sg = lambda z: (d + n) * z[0] + (d - n) * z[1]
    Hspec = set(range(2, L - 1, 2)) | set(range(n, d + 1, 2))
    Vspec = set(range(0, 2 * n + 1, 2)) | set(range(2 - d + n, L - 1, 2))
    Hb = [z for z in reps if not inE((z[0], z[1] - 1)) and tg(z) in Hspec]
    Vb = [z for z in reps if not inE((z[0] - 1, z[1])) and sg(z) in Vspec]
    return fu, Hb, Vb, inE


def run(w):
    w = list(w)
    fr = oc.frame(w)
    N, D, n, d = fr["N"], fr["D"], fr["n"], fr["d"]
    Lp, Tp = D + N, D * D + 2 * D * N - N * N
    u = list(pl.swap(pl.odd_birth_prefix(w)))
    out = defaultdict(int)
    if not u:
        out["u empty"] += 1
        return out
    fu, Hb, Vb, inE = conj_free(u)
    out[("conj child == (D-N, D+N)", (fu["n"], fu["d"]) == (D - N, D + N))] += 1
    Fu, _ = pl.standard(tuple(u))
    Jq = cut_on(Fu, u, 0, 1, 1)
    par = lambda x: (x[0] + x[1]) % 2 == 0
    for y in Hb:
        x = (y[1] + 1, -y[0])
        tp = N * x[0] - D * x[1]
        r = tp % Tp
        ok_x = (par(x) and 1 <= r <= Lp - 1) or ((not par(x)) and N <= r <= D)
        ok_y = (par(y) and 1 <= r <= Lp - 1) or ((not par(y)) and N <= r <= D)
        out[("H web, label x", ok_x)] += 1
        out[("H web, label y", ok_y)] += 1
        out["H sites"] += 1
    for y in Vb:
        x = (y[1] + 1, -y[0])
        sp = (D + N) * x[0] + (D - N) * x[1]
        r = sp % (2 * Tp)
        ok_x = (par(x) and 0 <= r <= 2 * N) or ((not par(x)) and 2 - D + N <= r <= Lp - 2)
        ok_y = (par(y) and 0 <= r <= 2 * N) or ((not par(y)) and 2 - D + N <= r <= Lp - 2)
        out[("V web, label x", ok_x)] += 1
        out[("V web, label y", ok_y)] += 1
        out["V sites"] += 1
        out[("a in {0,1}", Jq(y) in (0, 1))] += 1
    # drop 1 -> 0 on conjugate V sites under the prescribed kept edge (eta = +1)
    fu_n, fu_d = fu["n"], fu["d"]
    L = fu_n + fu_d
    for y in Vb:
        if Jq(y) != 1:
            continue
        if oc.even_site(y):
            dv = (1, 0)
        else:
            dv = (0, -1)
        t = (y[0] + dv[0], y[1] + dv[1])
        if Jq(t) == 0:
            out[("drop 1->0 target in polygon (j=0)", inE(t))] += 1
    return out


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    with Pool(12) as pool:
        for out in pool.imap_unordered(run, ws):
            for k, v in out.items():
                tot[k] += v
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
