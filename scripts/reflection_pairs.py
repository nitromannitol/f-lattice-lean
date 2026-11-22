"""Pairwise reflection search: an eps = -1 word w against an eps = +1 word v (both among the 116 proper words of length
<= 4), and a candidate affine map R(z) = M z + t applied to the sites of w's window.

Identities tested (exact equality on the window of w, one constant each):
  (a) Psi_v(R z) = s Psi_w(z) + c            s = +1 or -1
  (b) A_v(R z) = C_w(z) + c  and  C_v(R z) = A_w(z) + c      (the sheets of w exchanged into v)
  (c) A_v(R z) = A_w(z) + c  and  C_v(R z) = C_w(z) + c      (the sheets matched sheet to sheet)
Models (Fp, Xi, off) are computed once per word. Early exit on the first mismatch.
A hit is a candidate transfer of the eps = -1 sheet statement to the eps = +1 statement for v.
"""
import sys
from collections import Counter

import open_inputs_check as oc
import permit_local as pl
import reflection_search as rs


def sheets_of(w):
    Fp, Xi, off = pl.model(w)
    fr = oc.frame(w)
    shift, offset, const = fr["shift"], fr["offset"], fr["constant"]
    nq, dq = fr["nq_"], fr["dq_"]
    cache_A, cache_C = {}, {}

    def A(z):
        if z not in cache_A:
            cache_A[z] = Fp((z[0] - shift[0], z[1] - shift[1]))
        return cache_A[z]

    def C(z):
        if z not in cache_C:
            x = (z[0] - shift[0], z[1] - shift[1])
            cache_C[z] = Fp((x[0] - offset[0], x[1] - offset[1])) + (nq * x[0] - dq * x[1]) + const
        return cache_C[z]

    return fr, A, C


def run_pairs(maxlen):
    words = list(pl.proper_words(maxlen))
    minus = [w for w in words if oc.frame(w)["eps"] == -1]
    plus = [w for w in words if oc.frame(w)["eps"] == 1]
    S = {w: sheets_of(w) for w in words}
    hits = Counter()
    examples = {}
    for w in minus:
        fr_w, Aw, Cw = S[w]
        pts = rs.window_points(fr_w)
        trans = rs.translations(fr_w)
        for v in plus:
            _, Av, Cv = S[v]
            for mi, M in enumerate(rs.DIHEDRAL):
                for tname, t in trans.items():
                    def R(z, M=M, t=t):
                        p = rs.apply(M, z)
                        return (p[0] + t[0], p[1] + t[1])
                    imgs = [R(z) for z in pts]
                    # (a)
                    for s in (1, -1):
                        c0 = None
                        ok = True
                        for z, r in zip(pts, imgs):
                            val = (Cv(r) - Av(r)) - s * (Cw(z) - Aw(z))
                            if c0 is None:
                                c0 = val
                            elif val != c0:
                                ok = False
                                break
                        if ok:
                            hits[("a", mi, tname, s)] += 1
                            examples.setdefault(("a", mi, tname, s), (w, v))
                    # (b)
                    c1 = c2 = None
                    ok = True
                    for z, r in zip(pts, imgs):
                        x1 = Av(r) - Cw(z)
                        x2 = Cv(r) - Aw(z)
                        if c1 is None:
                            c1, c2 = x1, x2
                        elif x1 != c1 or x2 != c2:
                            ok = False
                            break
                    if ok:
                        hits[("b", mi, tname)] += 1
                        examples.setdefault(("b", mi, tname), (w, v))
                    # (c)
                    c1 = c2 = None
                    ok = True
                    for z, r in zip(pts, imgs):
                        x1 = Av(r) - Aw(z)
                        x2 = Cv(r) - Cw(z)
                        if c1 is None:
                            c1, c2 = x1, x2
                        elif x1 != c1 or x2 != c2:
                            ok = False
                            break
                    if ok:
                        hits[("c", mi, tname)] += 1
                        examples.setdefault(("c", mi, tname), (w, v))
    return len(minus), len(plus), hits, examples


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    nm, np_, hits, ex = run_pairs(maxlen)
    print("eps=-1 words", nm, " eps=+1 words", np_)
    if not hits:
        print("no pair (w eps=-1, v eps=+1) and candidate map satisfies any identity exactly")
    for key, cnt in hits.most_common(20):
        print("candidate", key, "pairs", cnt, "example (w, v)", ex[key])
