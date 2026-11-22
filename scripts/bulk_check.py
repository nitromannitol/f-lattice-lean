"""Archive input 'bulk monotonicity' for S3 on all 116 words: along every permitted edge z -> a (slip permits with +sigma),
P(a) <= P(z) and J(a) <= J(z), where P = cutGrade F 1 0 1 and J = cutGrade F 0 1 1 (eta = +1).
P and J differences along an edge are deck invariant, so it suffices to test the cover representatives.
Also PermitLocal (laplacian -1: both inputs permitted; laplacian 0: one permitted)."""
import sys
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, words

def run(w):
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    F, _ = pl.standard(tuple(w))
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, 1)
    det, S0 = re_.cover_sites(K, V)
    viol_P = viol_J = viol_any = 0
    ex = []
    locality_bad = 0
    for z in S0:
        l = lap(z)
        a1, a2 = pl.neighbours(z)
        p1, p2 = perm(z, a1), perm(z, a2)
        if l == -1 and not (p1 and p2):
            locality_bad += 1
        if l == 0 and not (p1 or p2):
            locality_bad += 1
        for a, pa in ((a1, p1), (a2, p2)):
            if not pa:
                continue
            dP = P(a) - P(z)
            dJ = J(a) - J(z)
            if dP > 0 or dJ > 0:
                viol_any += 1
                viol_P += dP > 0
                viol_J += dJ > 0
                if len(ex) < 3:
                    ex.append((z, a, dP, dJ))
    return tuple(w), len(S0), viol_P, viol_J, viol_any, locality_bad, ex

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, viol_P=0, viol_J=0, viol_any=0, locality=0, words_viol=0)
    with Pool(12) as pool:
        for w, n, vP, vJ, va, lb, ex in pool.imap_unordered(run, ws):
            tot["classes"] += n
            tot["viol_P"] += vP
            tot["viol_J"] += vJ
            tot["viol_any"] += va
            tot["locality"] += lb
            tot["words_viol"] += (va > 0)
            if va or lb:
                print("WORD", w, "viol", va, "P", vP, "J", vJ, "locality_bad", lb, "ex", ex[:2], flush=True)
    print("TOTAL", tot, flush=True)
