"""Closure test of E = {grade < L} U F1 (first-layer escapes) on the interior of a window.

If for every site u with grade(u) >= L, u not in E, the escape rule fails with respect to E (no site outside E can
escape from E in one step), then E is closed. Its complement U = {grade >= L} minus E is then a restricted fort in the
half-space {grade >= L}: every u in U is blocked by an input in U (inputs of u in E are either below the level, which
is escaped, or in F1), or by a non-permitted input.
"""
import sys
import restricted_escape as re_


def check(name, w, s, R, Rint):
    systems, fr = re_.systems_for(w)
    lap, perm, grade, K, V = systems[name]
    L = grade(s)
    cx, cy = s
    W = [(x, y) for x in range(cx - R, cx + R + 1) for y in range(cy - R, cy + R + 1)]
    inW = set(W)
    below = lambda z: grade(z) < L
    F1 = set()
    for z in W:
        if grade(z) >= L and lap(z) == 0:
            a, b = re_.neighbours(z)
            if below(a) or below(b):
                # first layer: lap-0 site with an input below the level, which escapes when that input is permitted
                if (below(a) and perm(z, a)) or (below(b) and perm(z, b)):
                    F1.add(z)
    E = lambda z: below(z) or (z in F1)
    # closure on interior: every site with inputs in W and grade >= L not in E must not escape from E
    viol = 0
    U_int = 0
    for z in W:
        if abs(z[0] - cx) > Rint or abs(z[1] - cy) > Rint:
            continue
        if grade(z) < L or z in F1:
            continue
        U_int += 1
        a, b = re_.neighbours(z)
        l = lap(z)
        pa, pb = perm(z, a), perm(z, b)
        ea, eb = E(a), E(b)
        rule = (l == -1 and pa and pb and ea and eb) or (l == 0 and ((pa and ea) or (pb and eb)))
        if rule:
            viol += 1
    return L, len(F1), U_int, viol


if __name__ == "__main__":
    w = [int(c) for c in sys.argv[1].split(",")]
    name = sys.argv[2]
    systems, fr = re_.systems_for(w)
    lap, perm, grade, K, V = systems[name]
    det, S0 = re_.cover_sites(K, V)
    fails = []
    for s in S0:
        esc, W = re_.escape_fixpoint(s, 12, lap, perm, grade, grade(s))
        if s not in esc:
            fails.append(s)
    print("word", w, name, "cover", len(S0), "failing cover sites (R=12):", len(fails))
    for s in fails[:4]:
        L, nF1, nU, viol = check(name, w, s, 24, 16)
        print("  site", s, "level", L, "first layer", nF1, "interior unescaped", nU, "closure violations", viol)
