"""The midpoint identity of the seventh copy with the odd target of its donor (task 46).

For a non-base even word w = p d with the donor tile altodd(p) (the odd alternate output of p), the seventh copy S(w) satisfies
on its sites
    H(w)(s) = P(s - T) + Js . s + k,     P = alternateOddTarget(p) = Q(p)(x - a(p)) + J(p) . x,
with T = offset_7(w) + R(w) (the seventh jet offset and the restoration), Js = slope of the seventh jet, a(p) the chart of p
(odd_chart_formula.py). This script takes R = 0 and reports whether the identity holds with one constant on the copy sites.
"""
import alt_copy_check as acc
from odd_donor_jet import H_of, Q_of
from seventh_jet import seventh_jet, parents_of, phase
from alt_jets import alternate_jets, lexmin

copy = acc.parse_dump(acc.DUMP)


def main():


    def chart(p):
        (N, D), (nq, dq) = parents_of(p)
        ph = phase(p)
        if ph == 0:
            return (0, 0), (0, 0)
        oT = (N - D, N + D)
        eK = (dq, nq)
        delta = (oT[0] - eK[0], oT[1] - eK[1])
        offs = [j[0] for j in alternate_jets(p, "odd")]
        from alt_jets import seventh_offset_slope
        offs.append(seventh_offset_slope(p, "odd")[0])
        LL = lexmin(offs)
        return (delta[0] - LL[0], delta[1] - LL[1]), (N, -D)


    def P_of(p):
        a, J = chart(p)
        Q = Q_of(list(p))
        return lambda x: Q((x[0] - a[0], x[1] - a[1])) + J[0] * x[0] + J[1] * x[1]


    for w in sorted([w for w in copy if len(w) >= 2 and w[-1] in (1, 2) and not all(d == 2 for d in w)], key=lambda t: (len(t), t)):
        p = w[:-1]
        if all(d == 3 for d in p):
            continue
        Hw = H_of(list(w))
        Js = seventh_jet(w)[1]
        J0 = seventh_jet(w)[0]
        P = P_of(p)
        ks = set()
        for (s, hs) in copy[w]["seventh"]:
            ks.add(Hw(s) - (P((s[0] - J0[0], s[1] - J0[1])) + Js[0] * s[0] + Js[1] * s[1]))
        print(w, "p", p, "chart(p)", chart(p)[0], "seventh offset", J0, "constants on copy sites:", sorted(ks)[:4], "one constant" if len(ks) == 1 else "NOT one constant", flush=True)


if __name__ == "__main__":
    main()
