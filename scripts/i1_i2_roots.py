"""Numerical check of the written steps behind (I1) root values and (I2) nontied roots, on the 116 proper words.

Uses open_inputs_check.frame / in_polygon / window and permit_local.model (Fp, Xi, off), as in open_inputs_check.py.
Sheets (Lean sheetA, sheetC): A(z) = Fp(z - shift), C(z) = Fp(z - shift - offset) + slope(z - shift) + constant.
h0 = harmonicGrid.

(I1 roots, H_SOURCE_ANCESTRAL_CLOSURE §2-3)
  Child H points, indexed j = 0..d-1, H_j = (j + 1, ceil(n (j + 1) / d) - 1)  (so H_0 = (1, 0), H_{d-1} = (d, n - 1)).
  W0 (eps = 1): w_j = H_j.   W1 (eps = -1): w_j = U + (1, -1) - H_j with U = (d, n).
  Claims checked:
    R1  w_j lies in E for every j;
    R2  Psi(w_0) = 0 and Psi(w_1) = 1 (exceptional endpoint, calibrated);
    R3  j -> Psi(w_j) is nondecreasing (the V-trace monotonicity of §1, stated as a check, not used as a proof);
    R4  Psi(w_j) >= 1 for j >= 1 (nontied roots).
    R5  C(w_0) = h0(w_0) and A(w_0) = 0 (the direct calibration of §3), and the same at w_1.

(I2 nontied roots, V_SOURCE_MONOTONICITY_AUDIT, eps = 1)
  Root w in E with s(w) <= 2(d + n) - 1 and Psi(w) >= 1; inputs u in {incomingNeg w, incomingPos w}.
    S1  A(u) = h0(u) for u in {w} union inputs(w)        (the "A agrees with h0 on the star" premise)
    S2  then min(A, C) = h0 on the star, and C(u) >= h0(u) for the inputs.
"""
import sys

import open_inputs_check as oc
import permit_local as pl


def h0(z):
    return pl.h0(z[0], z[1])


def sheets(w):
    Fp, Xi, off = pl.model(w)
    fr = oc.frame(w)
    shift, offset, const = fr["shift"], fr["offset"], fr["constant"]
    nq, dq = fr["nq_"], fr["dq_"]

    def A(z):
        return Fp((z[0] - shift[0], z[1] - shift[1]))

    def C(z):
        x = (z[0] - shift[0], z[1] - shift[1])
        return Fp((x[0] - offset[0], x[1] - offset[1])) + (nq * x[0] - dq * x[1]) + const

    return fr, A, C


def H_points(fr):
    n, d = fr["n"], fr["d"]
    return [(j + 1, -((-(n * (j + 1))) // d) - 1) for j in range(d)]


def check_roots(w):
    fr, A, C = sheets(w)
    d, n, eps = fr["d"], fr["n"], fr["eps"]
    H = H_points(fr)
    # archive W0 is W = (1 + eps)/2 = 0, i.e. eps = -1: w_j = H_j; archive W1 (eps = +1): w_j = U + (1,-1) - H_j
    if eps == -1:
        ws = H
    else:
        ws = [(d + 1 - x, n - 1 - y) for (x, y) in H]
    Psi = lambda z: C(z) - A(z)
    out = dict(in_E=0, not_in_E=0, psi0=None, psi1=None, monotone=True, ge1_fail=0,
               calib_fail=0, prev=None)
    vals = []
    for j, z in enumerate(ws):
        if oc.in_polygon(z, fr):
            out["in_E"] += 1
        else:
            out["not_in_E"] += 1
        vals.append(Psi(z))
    out["psi0"] = vals[0]
    out["psi1"] = vals[1] if len(vals) > 1 else None
    for j in range(1, len(vals)):
        if vals[j] < vals[j - 1]:
            out["monotone"] = False
    for j in range(1, len(vals)):
        if vals[j] < 1:
            out["ge1_fail"] += 1
    # R5: direct calibration at the two exceptional points j = 0, 1.
    # eps = -1 (archive W0): C(w) = h0(w);  eps = +1 (archive W1): C(w) = h0(w - U), U = (d, n).
    for z in ws[:2]:
        target = h0(z) if eps == -1 else h0((z[0] - d, z[1] - n))
        if A(z) != 0 or C(z) != target:
            out["calib_fail"] += 1
    return out


def sp_guard(fr, u):
    # archive: -2 dp + 1 <= sp(u) <= 2 dp + 2 np - 1 with sp = (dp + np) x + (dp - np) y, dp = D, np = N (odd parent)
    dp, np_ = fr["D"], fr["N"]
    s = (dp + np_) * u[0] + (dp - np_) * u[1]
    return -2 * dp + 1 <= s <= 2 * dp + 2 * np_ - 1


def check_I2(w):
    fr, A, C = sheets(w)
    d, n, eps = fr["d"], fr["n"], fr["eps"]
    res = dict(stars=0, nontied=0, S1_fail=0, S2_fail=0, guard_out=0, S1_guarded_fail=0)
    if eps != 1:
        return res
    x0, x1, y0, y1 = oc.window(fr)
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            w_ = (x, y)
            if not oc.in_polygon(w_, fr):
                continue
            if (d + n) * x + (d - n) * y > 2 * (d + n) - 1:
                continue
            res["stars"] += 1
            if C(w_) - A(w_) < 1:
                continue
            res["nontied"] += 1
            star = [w_, oc.incoming_neg(w_), oc.incoming_pos(w_)]
            res["guard_out"] += sum(1 for u in star if not sp_guard(fr, u))
            if any(A(u) != h0(u) for u in star if sp_guard(fr, u)):
                res["S1_guarded_fail"] += 1
            if any(A(u) != h0(u) for u in star):
                res["S1_fail"] += 1
                continue
            if any(C(u) < h0(u) for u in star[1:]):
                res["S2_fail"] += 1
    return res


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    words = list(pl.proper_words(maxlen))
    tot = dict(in_E=0, not_in_E=0, monotone_fail=0, ge1_fail=0, calib_fail=0, psi0_bad=0, psi1_bad=0)
    I2 = dict(stars=0, nontied=0, S1_fail=0, S2_fail=0, guard_out=0, S1_guarded_fail=0)
    bad_words = []
    for w in words:
        r = check_roots(w)
        tot["in_E"] += r["in_E"]
        tot["not_in_E"] += r["not_in_E"]
        tot["monotone_fail"] += (not r["monotone"])
        tot["ge1_fail"] += r["ge1_fail"]
        tot["calib_fail"] += r["calib_fail"]
        tot["psi0_bad"] += (r["psi0"] != 0)
        tot["psi1_bad"] += (r["psi1"] != 1)
        if r["not_in_E"] or (not r["monotone"]) or r["ge1_fail"] or r["calib_fail"] or r["psi0"] != 0 or r["psi1"] != 1:
            bad_words.append(("roots", "".join(map(str, w)), r))
        q = check_I2(w)
        for k in I2:
            I2[k] += q[k]
        if q["S1_guarded_fail"] or q["S2_fail"]:
            bad_words.append(("I2", "".join(map(str, w)), q))
    print("proper words checked:", len(words), "max length", maxlen)
    print("roots (I1):", tot)
    print("I2 nontied (eps=+1):", I2)
    for item in bad_words[:15]:
        print("  ", item)
