"""Is the odd alternate target the quarter turn of H_- (or of the reflected H_+) with the odd parent slope?

For an odd word w (phase one and phase zero), u = swap w, F = standard field of u, sigma = alternateSigma(u) (from the frame of u),
H_eta(y) = ceil((F(y) + F(y + eta sigma)) / 2), and the quarter turn Q_eta(x) = H_eta(Z x) + h(x), Z(y) = (-y2, y1 - 1), h the harmonic grid.

The raw odd target is raw(x) = Q_+(x - delta) + J . x with J = (N, -D) the transverse slope of the odd parent (phase one), and the
alternate target (normalised by the lower-left site LL of the output) is alt(z) = raw(z + LL) - J . LL, so with the chart offset
T = delta - LL one has alt(z) = Q_+(z - T) + J . z.

The claim under test: alt(z) = Q_-(z - T) + g . z + c with g = J (the gradient of the integer affine correction), so the slope and the chart
offset T both come from the reflection. The control Q_+ is constant by construction. Tests run on the copy sites (z = s - LL).
"""
import ordinary_tile_check as otc
from odd_copy_check import copy as ODD
from seventh_jet import parents_of, phase
from alt_jets import lexmin
from odd_copy_candidates import Z, h, sub, add
from odd_seventh_check import raw_target

ns = otc.load_proto()
standard, Frame, swap = ns["standard"], ns["Frame"], ns["swap"]


def check(w):
    u = tuple(swap(list(w)))
    F = standard(u)[0]
    fr = Frame(list(u))
    sigma = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    (N, D), (nq, dq) = parents_of(w)
    ph = phase(w)
    J = (N, -D) if ph == 1 else (0, 0)
    delta = (N - D - dq, N + D - nq) if ph == 1 else (0, 0)
    sites = [s for (tag, lst) in ODD[w].items() for (s, _) in lst]
    LL = lexmin(sites)
    T = (delta[0] - LL[0], delta[1] - LL[1])
    raw = raw_target(w)

    def alt(z):
        x = add(z, LL)
        return raw(x) - (J[0] * LL[0] + J[1] * LL[1])

    def H(eta, y):
        a = F(y)
        b = F(add(y, (eta * sigma[0], eta * sigma[1])))
        return (a + b + 1) // 2  # ceil((a + b) / 2)

    def Q(eta, x):
        return H(eta, Z(x)) + h(x)

    zs = [sub(s, LL) for s in sites]

    def residual(fn, g):
        vals = set()
        for z in zs:
            vals.add(fn(z) - g[0] * z[0] - g[1] * z[1])
        return len(vals), sorted(vals)[:4]

    out = {}
    out["Q+ control (alt - Q+(z-T) - J.z)"] = residual(
        lambda z: alt(z) - Q(+1, sub(z, T)), J)
    out["Q- with gradient J"] = residual(lambda z: alt(z) - Q(-1, sub(z, T)), J)
    out["Q- with gradient -J"] = residual(lambda z: alt(z) - Q(-1, sub(z, T)), (-J[0], -J[1]))
    out["Q- with gradient 0"] = residual(lambda z: alt(z) - Q(-1, sub(z, T)), (0, 0))
    return out, u, sigma, (N, D), T, LL, len(zs)


if __name__ == "__main__":
    words = sorted([w for w in ODD if w and w[-1] in (1, 3) and not all(d == 3 for d in w)], key=lambda t: (len(t), t))
    summary = {}
    for w in words:
        out, u, sigma, NDp, T, LL, nz = check(w)
        ph = phase(w)
        for k, (count, _) in out.items():
            summary.setdefault((ph, k), []).append((w, count))
        print(w, "phase", ph, "sigma", sigma, "N,D", NDp, "T", T, "LL", LL, "sites", nz,
              {k: v[0] for k, v in out.items()}, flush=True)
    print("---- number of distinct residual values (1 means constant) ----")
    for key in sorted(summary, key=str):
        ones = sum(1 for (w, c) in summary[key] if c == 1)
        print(key, "constant on", ones, "of", len(summary[key]))
