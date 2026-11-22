from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import open_inputs_check as oic
from exact_quotient import words
from psi_black_odd import lapF

def run(w):
    w = list(w)
    Fp, Xi, _ = pl.model(w)
    fr = oic.frame(w)
    shift, offset, const = fr["shift"], fr["offset"], fr["constant"]
    nq, dq = fr["nq_"], fr["dq_"]
    def A(z):
        return Fp((z[0] - shift[0], z[1] - shift[1]))
    def C(z):
        x = (z[0] - shift[0], z[1] - shift[1])
        return Fp((x[0] - offset[0], x[1] - offset[1])) + (nq * x[0] - dq * x[1]) + const
    Psi = lambda z: C(z) - A(z)
    F, _ = pl.standard(tuple(w))
    N, Dd = pl.parents(w)[0]
    eps = fr["eps"]
    sig = (2 * eps * Dd, 2 * eps * N)
    D = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    Up = (2 * Dd, 2 * N); Uq = (dq, nq)
    X = Up if eps == 1 else Uq
    def incs(z):
        if (z[0] + z[1]) % 2 == 0:
            return [(z[0] - 1, z[1]), (z[0] + 1, z[1])]
        return [(z[0], z[1] - 1), (z[0], z[1] + 1)]
    x0, x1, y0, y1 = oic.window(fr)
    cnt = Counter()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            z = (x, y)
            if not oic.in_polygon(z, fr):
                continue
            dz = D(z)
            zx = (z[0] + X[0], z[1] + X[1])
            ok = dz == -min(0, Psi(zx))
            cnt["E"] += 1
            cnt["E_formula"] += ok
            isV = (not oic.in_polygon((x - 1, y), fr)) or (not oic.in_polygon((x + 1, y), fr))
            if isV:
                cnt["Varc"] += 1
                cnt["Varc_formula"] += ok
                if lapF(F, z) == -1: cnt["Varc_oddblack"] += 1
            else:
                cnt["nonV"] += 1
                cnt["nonV_formula"] += ok
            if lapF(F, z) == -1 and dz % 2 == 1:
                cnt["oddblack"] += 1
                cnt["oddblack_formula"] += ok
                # inputs: Psi monotone from input+X to center+X
                cnt["oddblack_psimono"] += all(Psi((i[0]+X[0], i[1]+X[1])) >= Psi(zx) for i in incs(z))
    cnt["eps_" + str(eps)] += 1
    return tuple(w), cnt

if __name__ == "__main__":
    tot = Counter()
    with Pool(12) as pool:
        for w, c in pool.imap_unordered(run, list(words(4))):
            tot.update(c)
    for k, v in sorted(tot.items()):
        print(k, v)
