"""Same-level AND-OR attractor (the argument's minimal-level descent). Within one (P,J) level a fort's continuation stays
at that level. Black (laplacian -1) is ranked when every permitted SAME-LEVEL input is ranked (vacuously if none);
white (laplacian 0) is ranked when some permitted input is strictly lower (cannot lie in the level fort) or some
permitted same-level input is ranked. Free classes are ranked from the start (forced free set: P increases on a permitted edge).
A non-free class left unranked lies in a level restricted fort, which RestrictedNoFort forbids."""
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, words

def run(w):
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    F, _ = pl.standard(tuple(w))
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, 1)
    n, S0, gP, lapv, eP, _ = build(K, V, lap, perm, P)
    _, _, gJ, _, eJ, _ = build(K, V, lap, perm, J)
    E = []
    for p in range(n):
        E.append([(q, gP[q] + wP - gP[p], gJ[q] + wJ - gJ[p], pf) for (q, wP, pf), (q2, wJ, pf2) in zip(eP[p], eJ[p])])
    free = [any(pf and dP > 0 for (q, dP, dJ, pf) in E[p]) for p in range(n)]
    ranked = list(free)
    changed = True
    while changed:
        changed = False
        for p in range(n):
            if ranked[p]:
                continue
            perms = [(q, dP, dJ) for (q, dP, dJ, pf) in E[p] if pf]
            same = [q for (q, dP, dJ) in perms if dP == 0 and dJ == 0]
            lower = any(dP < 0 or dJ < 0 for (q, dP, dJ) in perms)
            if lapv[p] == -1:
                ok = all(ranked[q] for q in same)
            else:
                ok = lower or any(ranked[q] for q in same)
            if ok:
                ranked[p] = True
                changed = True
    unranked = [S0[p] for p in range(n) if not ranked[p]]
    return tuple(w), n, sum(free), len(unranked), unranked[:3]

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, free=0, unranked=0, words_unranked=0)
    with Pool(12) as pool:
        for w, n, nf, un, ex in pool.imap_unordered(run, ws):
            tot["classes"] += n
            tot["free"] += nf
            tot["unranked"] += un
            tot["words_unranked"] += (un > 0)
            if un:
                print("WORD", w, "n", n, "free", nf, "unranked", un, "ex", ex, flush=True)
    print("TOTAL", tot, flush=True)
