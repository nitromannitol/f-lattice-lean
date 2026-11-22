"""Numerical check of the local inputs of the open premises (I1), (I2), (I3a) on the proper words of length <= 4.

Frame quantities follow the Lean definitions exactly (ChildFrame.lean, Sheets.lean, PeriodDeck.lean, Graph.lean):
  odd parent P = (N, D) and even parent Q = (nq, dq) of the word (parentsAt word), child n/d = 2P + Q,
  eps = N dq - nq D, W = (1 + eps)/2, U_q = (dq, nq), V_q = (nq - dq, nq + dq),
  sheetShift = (1 - W) U_q, sheetOffset = V_q + eps U_q, siblingSlope x = nq x1 - dq x2,
  sheetConstant = (T_q - dq - nq)/2 + 2W with T_q = dq^2 + 2 dq nq - nq^2,
  t(x) = n x1 - d x2, s(x) = (d + n) x1 + (d - n) x2,
  E (closedPolygon): even sites: 2 - T <= t <= d + n - 2, 0 <= s <= T + 2n;
                     odd sites:  n - T <= t <= d, 2 - d + n <= s <= T + d + n - 2, with T = d^2 + 2dn - n^2.
  A(z) = Fp(z - shift), C(z) = Fp(z - shift - offset) + slope(z - shift) + constant.
The field Fp, the chain potential Xi and the edge relation come from permit_local.py, which models
standardField and sheetChainPotential (Xi(x) = earlierChainPrice G P old new (-x2, x1 - 1)).

Checked per word (window = the bounding box of E, enlarged by 2 for the edge check):
  I1   : C - A >= 0 on E with t >= 1 - d                     (LocalPremises clause I1)
  I2   : eps = 1: C - A >= 0 on E with s <= 2(d+n) - 1; eps = -1: C - A <= 0 there   (clause I2)
  I3a  : |Xi(i) - Xi(c)| <= 1 for Edge i c, i.e. i in {incomingNeg c, incomingPos c}   (clause I3, unit increments)
  id   : C - A + Xi(z - shift) is constant on the box (the identity of sheetDifference_identifies)
"""
import sys
from fractions import Fraction
from math import floor, ceil

import permit_local as pl


def even_site(z):
    return (z[0] + z[1]) % 2 == 0


def incoming_neg(z):
    return (z[0] - 1, z[1]) if even_site(z) else (z[0], z[1] - 1)


def incoming_pos(z):
    return (z[0] + 1, z[1]) if even_site(z) else (z[0], z[1] + 1)


def frame(w):
    (N, D), (nq, dq) = pl.parents(list(w))
    eps = N * dq - nq * D
    n, d = 2 * N + nq, 2 * D + dq
    W = (1 + eps) // 2
    T_child = d * d + 2 * d * n - n * n
    T_q = dq * dq + 2 * dq * nq - nq * nq
    shift = ((1 - W) * dq, (1 - W) * nq)
    offset = (nq - dq + eps * dq, nq + dq + eps * nq)
    constant = (T_q - dq - nq) // 2 + 2 * W
    return dict(N=N, D=D, nq=nq, dq=dq, n=n, d=d, eps=eps, W=W, T=T_child,
                shift=shift, offset=offset, constant=constant, nq_=nq, dq_=dq)


def in_polygon(z, fr):
    n, d, T = fr["n"], fr["d"], fr["T"]
    t = n * z[0] - d * z[1]
    s = (d + n) * z[0] + (d - n) * z[1]
    if even_site(z):
        return 2 - T <= t <= d + n - 2 and 0 <= s <= T + 2 * n
    return n - T <= t <= d and 2 - d + n <= s <= T + d + n - 2


def window(fr):
    """Integer box containing E, from the corners of the parallelogram in (t, s)."""
    n, d, T = fr["n"], fr["d"], fr["T"]
    ts = (min(2 - T, n - T), max(d + n - 2, d))
    ss = (min(0, 2 - d + n), max(T + 2 * n, T + d + n - 2))
    xs, ys = [], []
    for t in ts:
        for s in ss:
            x = Fraction((d - n) * t + d * s, T)
            y = Fraction(-(d + n) * t + n * s, T)
            xs.append(x)
            ys.append(y)
    return (floor(min(xs)) - 2, ceil(max(xs)) + 2, floor(min(ys)) - 2, ceil(max(ys)) + 2)


def check_word(w):
    Fp, Xi, _ = pl.model(w)
    fr = frame(w)
    shift, offset, sl, const = fr["shift"], fr["offset"], None, fr["constant"]
    nq, dq = fr["nq_"], fr["dq_"]

    def A(z):
        return Fp((z[0] - shift[0], z[1] - shift[1]))

    def C(z):
        x = (z[0] - shift[0], z[1] - shift[1])
        return Fp((x[0] - offset[0], x[1] - offset[1])) + (nq * x[0] - dq * x[1]) + const

    # Sanity: the model's offset must agree with the one used in permit_local.model.
    _, _, off_model = pl.model(w)
    assert off_model == offset, (w, off_model, offset)

    x0, x1, y0, y1 = window(fr)
    d, n, eps = fr["d"], fr["n"], fr["eps"]
    I1_bad = I2_bad = I3_bad = 0
    I1_min = I2_min = None
    ident = None
    id_bad = 0
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            z = (x, y)
            if not in_polygon(z, fr):
                continue
            t = n * x - d * y
            s = (d + n) * x + (d - n) * y
            psi = C(z) - A(z)
            if t >= 1 - d:
                I1_min = psi if I1_min is None else min(I1_min, psi)
                if psi < 0:
                    I1_bad += 1
            if s <= 2 * (d + n) - 1:
                if eps == 1 and psi < 0:
                    I2_bad += 1
                if eps == -1 and psi > 0:
                    I2_bad += 1
                I2_min = psi if I2_min is None else min(I2_min, psi)
    # I3a and the identity, over the window enlarged by two.
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            c = (x, y)
            xc = Xi(c)
            for i in (incoming_neg(c), incoming_pos(c)):
                if abs(Xi(i) - xc) > 1:
                    I3_bad += 1
            z = c
            k = C(z) - A(z) + Xi((z[0] - shift[0], z[1] - shift[1]))
            if ident is None:
                ident = k
            elif k != ident:
                id_bad += 1
    return dict(I1_bad=I1_bad, I1_min=I1_min, I2_bad=I2_bad, I2_min=I2_min, I3_bad=I3_bad,
                id_bad=id_bad, eps=eps)


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    words = list(pl.proper_words(maxlen))
    totals = dict(I1_bad=0, I2_bad=0, I3_bad=0, id_bad=0)
    failing = []
    for w in words:
        r = check_word(w)
        for k in totals:
            totals[k] += r[k]
        if any(r[k] for k in totals):
            failing.append((w, {k: r[k] for k in totals if r[k]}))
    print("proper words checked:", len(words), "max length", maxlen)
    print("totals:", totals)
    for w, v in failing[:20]:
        print("  failing:", "".join(map(str, w)), v)
