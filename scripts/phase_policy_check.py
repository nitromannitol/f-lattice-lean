"""Phase-η policy data of the strong estimates (task 49, the I3 bridge): for each word u and η in {1, -1}, check that
(F2F3) a quota policy of the standard field with Φ_η nonincreasing along it exists, and (F2F4) a chain policy of h'_η = chainSheet η
whose reflection ξ ↦ R − w − ξ has quotas for h'_η and nondecreasing Φ_η, for some reflection (R, w) in a window.

Definitions (Lean): chainPotential η z = slip η z + price (z + η σ), slip η z = F z − F(z + η σ), price z = F z − F(z − v) − ε a·z,
chainSheet η z = F(z + η σ − v) + ε a·(z + η σ), σ = 2ε(D, N), v = ε(N − D, N + D), a = (N, −D), (N, D) the odd parent of u.
Per-centre conditions are exact: a quota policy restricted to input pairs exists iff every black centre has both inputs and every
white centre one input in its admissible set. The rank parts (RankWithIncrements) are not checked here.
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_tile_check as otc  # noqa: E402
import upper_attainment_check as uac  # noqa: E402

ns = otc.load_proto()
standard, Frame = ns["standard"], ns["Frame"]


def inc_neg(x):
    return (x[0] - 1, x[1]) if (x[0] + x[1]) % 2 == 0 else (x[0], x[1] - 1)


def inc_pos(x):
    return (x[0] + 1, x[1]) if (x[0] + x[1]) % 2 == 0 else (x[0], x[1] + 1)


def edge(y, x):  # Edge y x
    return y == inc_neg(x) or y == inc_pos(x)


words = [w for L in (1, 2, 3) for w in itertools.product((1, 2, 3), repeat=L) if any(d != 3 for d in w)]
BOX = 5
CENTRES = [(a, b) for a in range(-BOX, BOX + 1) for b in range(-BOX, BOX + 1)]


def run(u, eta):
    F = standard(tuple(u))[0]
    fr = Frame(list(u))
    N, D, eps = fr.N, fr.D, fr.eps
    sig = (2 * eps * D, 2 * eps * N)
    v = (eps * (N - D), eps * (N + D))
    a = (N, -D)
    cache = {}

    def Fc(z):
        if z not in cache:
            cache[z] = F(z)
        return cache[z]

    def add(z, k):
        return (z[0] + k[0], z[1] + k[1])

    def P(z):
        return Fc(z) - Fc((z[0] - v[0], z[1] - v[1])) - eps * (a[0] * z[0] + a[1] * z[1])

    def Phi(z):  # chainPotential eta z
        zs = (z[0] + eta * sig[0], z[1] + eta * sig[1])
        return (Fc(z) - Fc(zs)) + P(zs)

    def hp(z):  # chainSheet eta z
        zs = (z[0] + eta * sig[0], z[1] + eta * sig[1])
        return Fc((zs[0] - v[0], zs[1] - v[1])) + eps * (a[0] * zs[0] + a[1] * zs[1])

    def lap(c):
        return (Fc(inc_neg(c)) - Fc(c)) + (Fc(inc_pos(c)) - Fc(c))

    # F2F3: quota policy of F with Φ_η nonincreasing along it (admissible input i of c: Φ(i) ≤ Φ(c))
    f23_ok = True
    for c in CENTRES:
        L = lap(c)
        if L not in (-1, 0):
            continue
        adm = [i for i in (inc_neg(c), inc_pos(c)) if Phi(i) <= Phi(c)]
        if L == -1 and len(adm) < 2:
            f23_ok = False
            break
        if L == 0 and len(adm) < 1:
            f23_ok = False
            break
    # F2F4: reflected chain policy; the reflection sigma(x) = R - w - x, admissible input i of c:
    # h'(σc) ≤ h'(σi), σi an input of σc, and Φ(c) ≤ Φ(i); quotas for h' from the laplacian of h'
    refl_found = None
    n_, d_ = fr.n, fr.d
    mu = 1 if (n_ + d_) % 2 == 0 else 2
    C = (mu * d_ + (n_ - d_) + 1, mu * n_ + (n_ + d_) - 1)
    R_range = None
    sv = sig; vv = v
    w_range = [(0, 0), sv, vv, (-sv[0], -sv[1]), (-vv[0], -vv[1]), (sv[0] + vv[0], sv[1] + vv[1]),
               (sv[0] - vv[0], sv[1] - vv[1]), (vv[0] - sv[0], vv[1] - sv[1]), (-sv[0] - vv[0], -sv[1] - vv[1])]
    hp_cache = {}
    def hpc(z):
        if z not in hp_cache:
            hp_cache[z] = hp(z)
        return hp_cache[z]
    Rs = [(C[0] + a1, C[1] + b1) for a1 in range(-3, 4) for b1 in range(-3, 4)]
    for R in Rs:
        for w in w_range:
            def sigma(x, R=R, w=w):
                return (R[0] - w[0] - x[0], R[1] - w[1] - x[1])
            ok = True
            for c in CENTRES:
                sc = sigma(c)
                lapc = (hpc(inc_neg(c)) - hpc(c)) + (hpc(inc_pos(c)) - hpc(c))
                if lapc not in (-1, 0):
                    continue
                adm = []
                for i in (inc_neg(c), inc_pos(c)):
                    si = sigma(i)
                    if hpc(sc) <= hpc(si) and edge(si, sc) and Phi(c) <= Phi(i):
                        adm.append(i)
                if lapc == -1 and len(adm) < 2:
                    ok = False
                    break
                if lapc == 0 and len(adm) < 1:
                    ok = False
                    break
            if ok:
                refl_found = (R, w)
                break
        if refl_found:
            break
    return f23_ok, refl_found


if __name__ == "__main__":
    summary = {1: [0, 0], -1: [0, 0]}
    for u in words:
        fr = Frame(list(u))
        row = []
        for eta in (1, -1):
            f23, refl = run(u, eta)
            summary[eta][0] += f23
            summary[eta][1] += refl is not None
            row.append(f"eta={eta:+d}: F2F3 {'ok' if f23 else 'FAIL'}, F2F4 {'refl '+str(refl) if refl else 'NONE'}")
        print(u, "eps", fr.eps, " | ".join(row), flush=True)
    print("summary (eta: F2F3 ok count, F2F4 found count) over", len(words), "words:", summary)
