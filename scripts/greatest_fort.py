"""Greatest fort inside the unescaped set of a window, for a restricted-fort system (Lean IsRestrictedFort).

A fort F: every u in F is blocked by F: laplacian -1 needs (neg in F or not permitted) or (pos in F or not permitted);
laplacian 0 needs (neg blocked) and (pos blocked). The greatest fort inside X is obtained by removing every site of X
that is not blocked by the current set. A nonempty result is a self-contained finite fort in the grade half-space
{grade >= level}, which refutes RestrictedNoFort for that level.
"""
import restricted_escape as re_


def blocked(u, F, lap, perm):
    a, b = re_.neighbours(u)
    ba = (a in F) or (not perm(u, a))
    bb = (b in F) or (not perm(u, b))
    l = lap(u)
    if l == -1:
        return ba or bb
    if l == 0:
        return ba and bb
    return False


def greatest_fort(X, lap, perm):
    F = set(X)
    changed = True
    while changed:
        changed = False
        for u in list(F):
            if not blocked(u, F, lap, perm):
                F.discard(u)
                changed = True
    return F


def fort_at_level(s, R, lap, perm, grade, L):
    esc, W = re_.escape_fixpoint(s, R, lap, perm, grade, L)
    X = {u for u in W if u not in esc and grade(u) >= L}
    return greatest_fort(X, lap, perm), X


if __name__ == "__main__":
    import sys
    w = [int(c) for c in sys.argv[1].split(",")] if len(sys.argv) > 1 else [2, 2]
    name = sys.argv[2] if len(sys.argv) > 2 else "S3"
    systems, fr = re_.systems_for(w)
    lap, perm, grade, K, V = systems[name]
    det, S0 = re_.cover_sites(K, V)
    for R in (10, 20, 30):
        bad = 0
        sizes = []
        for s in S0:
            F, X = fort_at_level(s, R, lap, perm, grade, grade(s))
            if F:
                bad += 1
                sizes.append(len(F))
        print("word", w, name, "R", R, "cover", len(S0), "cover sites with nonempty greatest fort:", bad,
              "sizes (first 5):", sizes[:5], flush=True)
