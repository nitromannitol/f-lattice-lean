"""Reflected-orientation test of the odd alternate target (task 46).

Frame of a word u (proto2.Frame): child frame with eps, D, N, U (kernel), V (transverse), t(z) = n z1 - d z2, L = d + n,
T = period denominator. The packet centre is R = U + V + (1, -1) and the reflection constant is kappa = (L - T)/2 (Bands.lean:
centre, symmetryConstant). The check (1): the standard even field F of u satisfies F(R - z) = F(z) - t(z) + kappa exactly.
The check (2): the alternate midpoint H(z) = ceil((F(z) + F(z + sigma))/2), sigma = 2 eps (D, N), satisfies
H(RH - z) = H(z) - t(z) + kappa + 1 with the shifted centre RH = R - sigma (the midpoint reflects about the average of the
two centres), up to the ceiling. Check (3): the odd alternate target variants for the 13 odd-phase words and the 10 even-phase
words, at zero translation, with the centre R or RH of the frame of the candidate word u (u = swap w, swap of the prefix
before the last 1 or 2, w itself).
"""
import sys

import ordinary_tile_check as otc
import alt_plane_check as apc


def midpoint(ns, u):
    standard, Frame = ns["standard"], ns["Frame"]
    F = standard(tuple(u))[0]
    fr = Frame(list(u))
    sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    G = lambda z: F((z[0] + sig[0], z[1] + sig[1]))
    H = lambda z: -((-(F(z) + G(z))) // 2)
    R = (fr.U[0] + fr.V[0] + 1, fr.U[1] + fr.V[1] - 1)
    RH = (R[0] - sig[0], R[1] - sig[1])
    return F, H, fr, R, RH


def residual_counts(fn, centre, fr, kappa_shift, window=10):
    counts = {}
    for x in range(-window, window + 1):
        for y in range(-window, window + 1):
            z = (x, y)
            r = fn((centre[0] - x, centre[1] - y)) - fn(z) + fr.t(z) - ((fr.L - fr.T) // 2) - kappa_shift
            counts[r] = counts.get(r, 0) + 1
    return counts


def prefix_before_last_12(w):
    ks = [i for i, x in enumerate(w[:-1]) if x in (1, 2)]
    return w[: ks[-1]] if ks else []


def main():
    ns = otc.load_proto()
    h0, swap = ns["h0"], ns["swap"]

    print("(1) standard field, F(R - z) - F(z) + t(z) - kappa:")
    for s in ["1", "12", "13", "21", "123"]:
        u = [int(c) for c in s]
        F, H, fr, R, RH = midpoint(ns, u)
        print("   ", s, "R", R, "residual", residual_counts(F, R, fr, 0))

    print("(2) midpoint H, centre RH = R - sigma, residual minus constant kappa + 1:")
    for s in ["1", "12", "13", "21", "123", "231"]:
        u = [int(c) for c in s]
        F, H, fr, R, RH = midpoint(ns, u)
        print("   ", s, "RH", RH, "residual", residual_counts(H, RH, fr, 1))

    words = apc.parse_log(apc.DATA)
    rows = []
    for e in words:
        w = e["word"]
        if not apc.ordinary(w, "odd") or not e["odd"]:
            continue
        phase = sum(1 for d in w if d == 1) % 2
        rows.append((list(w), phase, e["odd"]))

    def candidate(name, w):
        if name == "swap(w)":
            return swap(w)
        if name == "swap(w[:-1])":
            return swap(w[:-1])
        if name == "swap(prefix before last 1|2)":
            return swap(prefix_before_last_12(w))
        if name == "w":
            return list(w)
        raise KeyError(name)

    def target(variant, u, centre_name, w):
        _, H, fr, R, RH = midpoint(ns, u)
        c = {"R": R, "RH": RH}[centre_name]
        if variant == "plain":
            return lambda x: H((-x[1], x[0] - 1)) + h0(*x)
        if variant == "reflect inside":
            return lambda x: H((c[0] + x[1], c[1] - (x[0] - 1))) + h0(*x)
        if variant == "reflect quarter":
            return lambda x: H((-(c[1] - x[1]), (c[0] - x[0]) - 1)) + h0(c[0] - x[0], c[1] - x[1])
        if variant == "reflect harmonic":
            return lambda x: H((-x[1], x[0] - 1)) + h0(c[0] - x[0], c[1] - x[1])
        raise KeyError(variant)

    print("(3) odd alternate variants at zero translation: fits of (phase 0, 10 words), (phase 1, 13 words)")
    for cand in ["swap(w)", "swap(w[:-1])", "swap(prefix before last 1|2)", "w"]:
        for centre in ["RH", "R"]:
            for variant in ["plain", "reflect inside", "reflect quarter", "reflect harmonic"]:
                fits = {0: 0, 1: 0}
                tot = {0: 0, 1: 0}
                for w, phase, sites in rows:
                    tot[phase] += 1
                    u = candidate(cand, w)
                    tgt = target(variant, u, centre, w)
                    if otc.fit(sites, tgt, [(0, 0)]) is not None:
                        fits[phase] += 1
                print(f"    {cand:30s} centre {centre:2s} {variant:17s} phase0 {fits[0]}/{tot[0]}  phase1 {fits[1]}/{tot[1]}")


if __name__ == "__main__":
    sys.exit(main())
