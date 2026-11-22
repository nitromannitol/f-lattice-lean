from multiprocessing import Pool
from collections import Counter
import permit_local as pl
import open_inputs_check as oic
from exact_quotient import words

def lapF(F, z):
    if (z[0] + z[1]) % 2 == 0:
        a, b = (z[0] - 1, z[1]), (z[0] + 1, z[1])
    else:
        a, b = (z[0], z[1] - 1), (z[0], z[1] + 1)
    return F(a) + F(b) - 2 * F(z)

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
            if lapF(F, z) != -1 or (D(z) % 2) != 1:
                continue
            cnt["oddblack"] += 1
            dz = D(z)
            for name, X in Xs.items():
                zx = (z[0] + X[0], z[1] + X[1])
                if dz == -min(0, Psi(zx)):
                    cnt["Dformula_" + name] += 1
                ok = True
                for i in incs(z):
                    ix = (i[0] + X[0], i[1] + X[1])
                    if not (Psi(ix) >= Psi(zx)):
                        ok = False
                if ok:
                    cnt["Psi_mono_inputs_" + name] += 1
            # the actual rise test on D, for the record
            if any(D(i) > dz for i in incs(z)):
                cnt["rise"] += 1
    return tuple(w), cnt

if __name__ == "__main__":
    tot = Counter()
    with Pool(12) as pool:
        for w, c in pool.imap_unordered(run, list(words(4))):
            tot.update(c)
    for k, v in sorted(tot.items()):
        print(k, v)
