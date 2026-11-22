"""The seventh copy of the ordinary odd alternate (task 46).

For an ordinary odd word w = p d (d in {1, 3}), the seventh copy of its odd output is the even alternate of the parent p
(the register alteven(p), whose target is H(p)) restored by alternateRestoration(w, .even) and placed at the odd seventh jet.
In raw coordinates the odd target of w is Q(w)(x - delta) + J . x, with delta = phase(w) (transverse offset of the odd parent
minus the kernel offset of the even parent) and J the transverse slope of the odd parent (phase 1). This script searches the
translation T of the seventh copy relative to H(p) and reports the constant, and the raw target identity.
"""
import sys
import alt_copy_check as acc
import alt_plane_check as apc
from odd_donor_jet import H_of, Q_of
from seventh_jet import parents_of, phase
from alt_jets import alternate_jets, seventh_offset_slope

ODD_DUMP = "/Users/ahmedbou-rabee/lean-work/flattice-wt/w2/scripts/data/alt_copy_odd_dump.log"
copy = acc.parse_dump(ODD_DUMP)
plane = apc.parse_log(apc.DATA)
even_reg = {tuple(e["word"]): e["even"] for e in plane}


def seventh_odd(w):
    off, slope = seventh_offset_slope(w, "odd")
    return off, slope


def raw_target(w):
    """Q(w)(x - delta) + J.x in raw coordinates, as a function of x."""
    ph = phase(w)
    (N, D), (nq, dq) = parents_of(w)
    delta = ((N - D) - dq, (N + D) - nq) if ph == 1 else (0, 0)
    J = (N, -D) if ph == 1 else (0, 0)
    Q = Q_of(list(w))
    return lambda x: Q((x[0] - delta[0], x[1] - delta[1])) + J[0] * x[0] + J[1] * x[1]


if __name__ == "__main__":
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    for w in sorted([w for w in copy if len(w) >= 2 and w[-1] in (1, 3) and not all(d == 3 for d in w)],
                    key=lambda t: (len(t), t)):
        p = w[:-1]
        if p not in even_reg or all(d == 3 for d in p):
            print(w, "no donor register for", p, flush=True)
            continue
        Hp = H_of(list(p))
        off, Js = seventh_odd(w)
        sites = copy[w]["seventh"]
        hits = []
        for a in range(-R, R + 1):
            for b in range(-R, R + 1):
                ks = set(hs - (Hp((s[0] - a, s[1] - b)) + Js[0] * s[0] + Js[1] * s[1]) for (s, hs) in sites)
                if len(ks) == 1:
                    hits.append(((a, b), ks.pop()))
        hits.sort(key=lambda h: abs(h[0][0]) + abs(h[0][1]))
        # the raw target of w on the same sites: is it a constant shift of the copy?
        Rw = raw_target(w)
        rw_ks = set(hs - Rw(s) for (s, hs) in sites)
        print(w, "p", p, "seventh offset", off, "slope", Js, "phase", phase(w), "T candidates (T, k):", hits[:3],
              "| raw-target constant:", len(rw_ks) == 1, sorted(rw_ks)[:2], flush=True)
