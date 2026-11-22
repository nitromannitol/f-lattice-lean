"""Which standard expression each copy of the ordinary odd alternate matches up to a constant (task 46).

Candidates, for an odd word w (u = swap w, F = standard field of u, delta = chart_delta(w), chart = oddStdChart(w),
slope = alternateOddSlope(w), sigma = alternateSigma(u)), all in raw coordinates x:
  Pl(x)  = F(Z(x - delta)) + h(x - delta) + slope . x          (alternateOddPlane: the F-branch of the raw target)
  Pc(x)  = F(Z(x - chart)) + h(x - chart)                       (planeTarget at the chart shift)
  P0(x)  = F(Z(x)) + h(x)                                       (planeTarget at zero shift)
  Ps(x)  = F(Z(x - delta) + sigma) + h(x - delta) + slope . x  (the G-branch of the raw target, minus one)
  R(x)   = raw target (alternateOddRawTarget)
Z(y) = (-y2, y1 - 1); h = harmonicGrid. For each copy tag, prints the candidates it differs from by one constant on all its sites.
"""
import ordinary_tile_check as otc
from odd_copy_check import copy as ODD, TAGS
from seventh_jet import parents_of, phase
from alternate_chart import chart_delta

ns = otc.load_proto()
standard, Frame, swap = ns["standard"], ns["Frame"], ns["swap"]


def Z(y):
    return (-y[1], y[0] - 1)


def h(y):
    y1, y2 = y
    return (y1 * y1 + 2 * y1 * y2 - y2 * y2 - 2 * y2 - (y1 + y2) % 2) // 4


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def candidates(w):
    u = tuple(swap(list(w)))
    F = standard(u)[0]
    fr = Frame(list(u))
    sigma = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    (N, D), (nq, dq) = parents_of(w)
    ph = phase(w)
    delta = chart_delta(w)
    chart = (-dq, -nq) if ph == 1 else (0, 0)
    slope = (N, -D) if ph == 1 else (0, 0)

    def Pl(x):
        y = sub(x, delta)
        return F(Z(y)) + h(y) + slope[0] * x[0] + slope[1] * x[1]

    def Pc(x):
        y = sub(x, chart)
        return F(Z(y)) + h(y)

    def P0(x):
        return F(Z(x)) + h(x)

    def Ps(x):
        y = sub(x, delta)
        return F(add(Z(y), sigma)) + h(y) + slope[0] * x[0] + slope[1] * x[1]

    def R(x):
        y = sub(x, delta)
        z = Z(y)
        Fz = F(z)
        Fs = F(add(z, sigma)) + 1
        return min(Fz, Fs) + h(y) + slope[0] * x[0] + slope[1] * x[1]

    return {"Pl": Pl, "Pc": Pc, "P0": P0, "Ps": Ps, "R": R}, ph


def constant_candidates(sites, cands):
    out = []
    for name, f in cands.items():
        ks = set(hs - f(s) for (s, hs) in sites)
        if len(ks) == 1:
            out.append(name)
    return out


if __name__ == "__main__":
    words = sorted([w for w in ODD if w and w[-1] in (1, 3) and not all(d == 3 for d in w)], key=lambda t: (len(t), t))
    for w in words:
        cands, ph = candidates(w)
        row = []
        for t in TAGS:
            names = constant_candidates(ODD[w][t], cands)
            row.append(f"{t}:{'/'.join(names) if names else '-'}")
        print(w, "phase", ph, " ".join(row), flush=True)
