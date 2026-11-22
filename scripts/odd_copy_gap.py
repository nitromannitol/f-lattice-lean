"""Gap classes of the copies of the ordinary odd alternate (task 46).

For an odd word w (ends in 1 or 3, length at most three, not pure three), u = swap w, the odd raw target is quarter(H_u)(x - delta) +
slope . x with H_u the alternate midpoint of u. The gap of u at z = Z(x - delta), Z(y) = (-y2, y1 - 1), is G(z) = F_u(z) - F_u(z + sigma_u).
A copy is F-pure if G <= 1 on its sites (the copy is the shifted standard odd target), G-pure if G >= 2 on its sites (the copy is
the shifted target at z + sigma_u, plus one), mixed otherwise.
"""
import ordinary_tile_check as otc
from odd_copy_check import copy as ODD, TAGS
from seventh_jet import parents_of, phase
from odd_chart_formula import *  # noqa: F401,F403  (keeps the chart formulas consistent)

ns = otc.load_proto()
standard, Frame, swap = ns["standard"], ns["Frame"], ns["swap"]


def Z(y):
    return (-y[1], y[0] - 1)


def classes(w):
    u = tuple(swap(list(w)))
    F = standard(u)[0]
    fr = Frame(list(u))
    sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    from alternate_chart import chart_delta  # local helper below
    delta = chart_delta(w)
    out = {}
    for t in TAGS:
        vals = []
        for (s, _) in ODD[w][t]:
            z = Z((s[0] - delta[0], s[1] - delta[1]))
            vals.append(F(z) - F((z[0] + sig[0], z[1] + sig[1])))
        if max(vals) <= 1 and min(vals) >= 0:
            out[t] = "F-pure"
        elif min(vals) >= 2:
            out[t] = "G-pure"
        else:
            out[t] = f"mixed[{min(vals)},{max(vals)}]"
    return out, sig, delta


if __name__ == "__main__":
    for w in sorted([w for w in ODD if w and w[-1] in (1, 3) and not all(d == 3 for d in w)], key=lambda t: (len(t), t)):
        out, sig, delta = classes(w)
        print(w, "phase", phase(w), "sigma_u", sig, "delta", delta, out, flush=True)
