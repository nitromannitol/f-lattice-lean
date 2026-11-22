from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import open_inputs_check as oic
from exact_quotient import words

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
    Xs = {"0": (0, 0), "Up": Up, "-Up": (-Up[0], -Up[1]), "Uq": Uq, "-Uq": (-Uq[0], -Uq[1])}
    x0, x1, y0, y1 = oic.window(fr)
    cnt = Counter()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            z = (x, y)
            if not oic.in_polygon(z, fr):
                continue
            dz = D(z)
            cnt["E"] += 1
            for name, X in Xs.items():
                if dz == -min(0, Psi((z[0] + X[0], z[1] + X[1]))):
                    cnt["match_" + name] += 1
            cnt["D_" + str(dz)] += 1
    return tuple(w), cnt

if __name__ == "__main__":
    tot = Counter()
    with Pool(12) as pool:
        for w, c in pool.imap_unordered(run, list(words(3))):
            tot.update(c)
    print(sorted(tot.items()), flush=True)
