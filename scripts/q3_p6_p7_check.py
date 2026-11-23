"""Task 59 paragraphs 6 and 7 (field identities; checked numerically on words <= 4 before Lean):
f = quarterTurnField G = G(Zx) + h0(x), G = standard(u), u = swap(odd_birth_prefix(w)), Z x = (-x2, x1-1).
Paragraph 7 (reflection): T1  f(I - y) == f(y), I = (1,-1).
Paragraph 6: b(x) = f(x - V_q) - f(x) + a_q . x + c_e, a_q = (n_q, -d_q), V_q = (n_q-d_q, n_q+d_q), c_e = (T_q-d_q-n_q)/2 + 2W,
  T_q = d_q^2+2 d_q n_q - n_q^2, W = (1+eps)/2.
  T2  b(x) + D(Zx) constant in x for D(y) = G(y) - G(y + eta*sigma_c) (sigma_c = conj shortShift (2 eps_c D_c, 2 eps_c N_c)),
      tested for eta = +1 and -1; the constant is reported.
  T3  a(x) = f(x + eps U_q) - f(x) equals -p(x + eps U_q) (p(y) = f(y - eps U_q) - f(y)): a definitional check.
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    if all(x == 3 for x in w):
        return {}
    u = list(pl.swap(pl.odd_birth_prefix(w)))
    if not u:
        return {"conjugate empty, skipped": 1}
    G, _ = pl.standard(tuple(u))
    h0 = pl.h0
    fr = oc.frame(w)
    N, D, nq, dq, eps = fr["N"], fr["D"], fr["nq"], fr["dq"], fr["eps"]
    fc = oc.frame(u)
    Nc, Dc, epsc = fc["N"], fc["D"], fc["eps"]
    Z = lambda x: (-x[1], x[0] - 1)
    f = lambda x: G(Z(x)) + h0(*x)
    out = defaultdict(int)
    W = (1 + eps) // 2
    Vq = (nq - dq, nq + dq)
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    aq = (nq, -dq)
    sig_c = (2 * epsc * Dc, 2 * epsc * Nc)
    Ud = (dq, nq)
    x0, x1, y0, y1 = oc.window(fr)
    pts = [(a, b) for a in range(x0, x1 + 1) for b in range(y0, y1 + 1)]
    # T1: reflection
    ok1 = all(f((1 - y[0], -1 - y[1])) == f(y) for y in pts)
    out[("T1 f(I-y) == f(y) on window box", ok1)] += 1
    # T2: b(x) + D(Zx) constant
    for eta in (1, -1):
        vals = set()
        for x in pts:
            b = f((x[0] - Vq[0], x[1] - Vq[1])) - f(x) + (aq[0] * x[0] + aq[1] * x[1]) + ce
            zx = Z(x)
            Dv = G(zx) - G((zx[0] + eta * sig_c[0], zx[1] + eta * sig_c[1]))
            vals.add(b + Dv)
        out[("T2 eta=%+d: b + D(Zx) constant" % eta, len(vals) == 1)] += 1
        if len(vals) == 1:
            out[("T2 eta=%+d constant value" % eta, list(vals)[0])] += 1
    # T3: a(x) = -p(x + eps Uq) with p(y) = f(y - eps Uq) - f(y)
    ok3 = True
    for x in pts:
        ax = f((x[0] + eps * Ud[0], x[1] + eps * Ud[1])) - f(x)
        y = (x[0] + eps * Ud[0], x[1] + eps * Ud[1])
        py = f((y[0] - eps * Ud[0], y[1] - eps * Ud[1])) - f(y)
        if ax != -py:
            ok3 = False
            break
    out[("T3 a(x) = -p(x+eps Uq)", ok3)] += 1
    return out


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    with Pool(12) as pool:
        for out in pool.imap_unordered(run, ws):
            for k, v in out.items():
                if isinstance(k, tuple):
                    tot[k] += v
                else:
                    tot[k] += v
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
