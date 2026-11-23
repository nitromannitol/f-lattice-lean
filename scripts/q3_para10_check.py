"""Task 60 paragraph 10 (numerical, words <= 4): for the native block vertices v (child left V vertices, or the exceptional
V_p + I when W = 1) and x = v + i U_p with x, x + U_q in E (closed polygon):
  C1  s(U_q) = T - 2C   (C = D L + N (d-n), T = d^2 + 2dn - n^2, B0 = 2C = s(U_p));
  C2  l_chi - s(v) <= i B0 <= B0 + h_chi - s(v) (both x and x+U_q in E);
  C3  i in {0, 1} when s(v) in [l_chi, h_chi];  C4  i = 0 for the exceptional V_p + I (W = 1).
Here U_p = 2(D, N), U_q = (dq, nq), U = (d, n), parity chi = EvenSite; (l, h) = (0, 2n) even, (2-d+n, L-2) odd.
"""
from multiprocessing import Pool
from collections import defaultdict
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    fr = oc.frame(w)
    N, D, n, d, eps, T = fr["N"], fr["D"], fr["n"], fr["d"], fr["eps"], fr["T"]
    nq, dq = fr["nq"], fr["dq"]
    L = n + d
    C = D * L + N * (d - n)
    B0 = 2 * C
    W = (1 + eps) // 2
    sg = lambda z: L * z[0] + (d - n) * z[1]
    inE = lambda z: oc.in_polygon(z, fr)
    out = defaultdict(int)
    out[("C1 s(U_q) = T - 2C", sg((dq, nq)) == T - 2 * C)] += 1
    Up = (2 * D, 2 * N)
    Uq = (dq, nq)
    def lh(z):
        return (0, 2 * n) if oc.even_site(z) else (2 - d + n, L - 2)
    # the block: odd vertices v_l, l < D, plus V_p + I (exceptional when W = 1, child left when W = 0)
    verts = []
    for l in range(1, D + 1):
        bp = (d - n) * l // d            # child floor (equals the parent floor for l < D)
        verts.append(("odd", (-bp, 2 * l - 1 - bp)))
    verts.append(("exc", (N - D + 1, D + N - 1)))
    for kind, v in verts:
        # child left vertex test
        left = inE(v) and not inE((v[0] - 1, v[1]))
        for i in range(-4, 5):
            x = (v[0] + i * Up[0], v[1] + i * Up[1])
            xu = (x[0] + Uq[0], x[1] + Uq[1])
            if not (inE(x) and inE(xu)):
                continue
            l, h = lh(x)
            s = sg(v)
            ok_bounds = l - s <= i * B0 <= B0 + h - s
            out[("C2 bounds hold", ok_bounds)] += 1
            if kind == "odd" and left:
                out[("C3 i in {0,1} (child left vertex)", i in (0, 1))] += 1
            if kind == "exc":
                out[("C4 exceptional: W=%d, i = 0" % W, i == 0)] += 1
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
