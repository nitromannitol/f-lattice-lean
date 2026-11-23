"""Task 59 step 1: a in {0,1} on the child's native V sites (a = J of the child field), and the drop 1 -> 0 check
under the eta = +1 prescribed kept edges on the native V cut: a drop from J = 1 to J = 0 must have its target inside the
closed polygon (translate index 0)."""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import cut_on, words


def run(w):
    w = list(w)
    fr = oc.frame(w)
    n, d, L = fr["n"], fr["d"], fr["n"] + fr["d"]
    tgr = lambda z: n * z[0] - d * z[1]
    sgr = lambda z: L * z[0] + (d - n) * z[1]
    F, _ = pl.standard(tuple(w))
    J = cut_on(F, w, 0, 1, 1)
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    Vspec = set(range(0, 2 * n + 1, 2)) | set(range(2 - d + n, L - 1, 2))
    Vb = [z for z in reps if not inE((z[0] - 1, z[1])) and sgr(z) in Vspec]
    out = defaultdict(int)
    for z in Vb:
        out[("a in {0,1}", J(z) in (0, 1))] += 1
        if J(z) != 1:
            continue
        dv = (1, 0) if oc.even_site(z) else (0, -1)
        if dv == (1, 0):
            dv = (1, 0)  # eta = +1: eta east at even V sites
        t = (z[0] + dv[0], z[1] + dv[1])
        if J(t) == 0:
            out[("drop 1->0, target in E", inE(t))] += 1
        out["J=1 V sites checked"] += 1
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
