"""Task 59 paragraph 5 bound, numerical check (words <= 4): p(y) = c0 - P(Zy) with P = conj.price G, c0 = conj.cutPrice,
G = standard(u), u = swap(odd_birth_prefix(w)). e = V_q + eps U_q (sheetStep). Test p(x - e) >= p(x) - 1 for x in the window box
of w, and the floor sandwich p(y) in [parentFloor(y), parentFloor(y) + 1] for y in the same box.
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
    fr = oc.frame(w)
    N, D, nq, dq, eps = fr["N"], fr["D"], fr["nq"], fr["dq"], fr["eps"]
    fc = oc.frame(u)
    Nc, Dc, epsc = fc["N"], fc["D"], fc["eps"]
    Tpc = Dc * Dc + 2 * Dc * Nc - Nc * Nc
    c0 = (Tpc - epsc * (Dc + Nc)) // 2
    ps = (epsc * (Nc - Dc), epsc * (Nc + Dc))
    P = lambda z: G(z) - G((z[0] - ps[0], z[1] - ps[1])) - epsc * (Nc * z[0] - Dc * z[1])
    Z = lambda x: (-x[1], x[0] - 1)
    p = lambda y: c0 - P(Z(y))
    B = D * D + 2 * D * N - N * N
    phi = lambda y: (N * y[0] - D * y[1] - N) // B
    Vq = (nq - dq, dq + nq); Uq = (dq, nq)
    e = (Vq[0] + eps * Uq[0], Vq[1] + eps * Uq[1])
    out = defaultdict(int)
    x0, x1, y0, y1 = oc.window(fr)
    for zy in range(y0, y1 + 1):
        for zx in range(x0, x1 + 1):
            x = (zx, zy)
            xe = (x[0] - e[0], x[1] - e[1])
            out[("p(x-e) >= p(x) - 1", p(xe) >= p(x) - 1)] += 1
            out[("floor sandwich p(y) in [phi, phi+1]", phi(x) <= p(x) <= phi(x) + 1)] += 1
            out[("phi(x-e) >= phi(x)", phi(xe) >= phi(x))] += 1
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
