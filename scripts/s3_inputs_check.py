"""Check the Lean hypotheses of S3NoFortInputs on all 116 words for the candidate instantiation:
  free := forced set (a permitted input increases P);  bulkOrder := rank of the same-level attractor (level_attractor.py).
  bulkBlack: every non-free black class: every permitted input is weakly lower in P and J, and if equal in both
             then its rank is strictly smaller.
  bulkWhite: every non-free white class: some permitted input is weakly lower in P and J, and if equal in both then
             its rank is strictly smaller.
  endpoint gate, local necessary form (diagnostic only; the real gate quantifies over restricted forts):
    for a free class, the fort's blocking inputs: black needs one permitted input, white needs all permitted inputs;
    the archive requires each such input to be weakly lower with a strict inequality or an earlier same-level free site.
    We count free black classes with no permitted input of that kind, and free white classes with a permitted input of
    the wrong kind."""
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
    E = [[(q, gP[q] + wP - gP[p], gJ[q] + wJ - gJ[p], pf) for (q, wP, pf), (q2, wJ, pf2) in zip(eP[p], eJ[p])] for p in range(n)]
    free = [any(pf and dP > 0 for (q, dP, dJ, pf) in E[p]) for p in range(n)]
    # ranks of the same-level AND-OR attractor from the free set
    rank = [0 if free[p] else None for p in range(n)]
    step = 0
    while True:
        step += 1
        new = []
        for p in range(n):
            if rank[p] is not None:
                continue
            perms = [(q, dP, dJ) for (q, dP, dJ, pf) in E[p] if pf]
            same = [q for (q, dP, dJ) in perms if dP == 0 and dJ == 0]
            lower = any(dP < 0 or dJ < 0 for (q, dP, dJ) in perms)
            if lapv[p] == -1:
                ok = all(rank[q] is not None for q in same)
            else:
                ok = lower or any(rank[q] is not None for q in same)
            if ok:
                new.append(p)
        if not new:
            break
        for p in new:
            rank[p] = step
    bad_black = bad_white = unranked = 0
    for p in range(n):
        if free[p]:
            continue
        if rank[p] is None:
            unranked += 1
            continue
        perms = [(q, dP, dJ) for (q, dP, dJ, pf) in E[p] if pf]
        if lapv[p] == -1:
            for (q, dP, dJ) in perms:
                weak = dP <= 0 and dJ <= 0
                eqlev = dP == 0 and dJ == 0
                if not (weak and (not eqlev or rank[q] < rank[p])):
                    bad_black += 1
                    break
        else:
            ok = False
            for (q, dP, dJ) in perms:
                weak = dP <= 0 and dJ <= 0
                eqlev = dP == 0 and dJ == 0
                if weak and (not eqlev or rank[q] < rank[p]):
                    ok = True
                    break
            if not ok:
                bad_white += 1
    gate_black_none = gate_white_wrong = 0
    for p in range(n):
        if not free[p]:
            continue
        cert = [(q, dP, dJ, pf) for (q, dP, dJ, pf) in E[p] if pf and dP <= 0 and dJ <= 0 and (dP < 0 or dJ < 0)]
        same_free = [q for (q, dP, dJ, pf) in E[p] if pf and dP == 0 and dJ == 0 and free[q]]
        good = lambda: bool(cert or same_free)
        if lapv[p] == -1:
            if not good():
                gate_black_none += 1
        else:
            perms = [(q, dP, dJ, pf) for (q, dP, dJ, pf) in E[p] if pf]
            if not all((dP <= 0 and dJ <= 0 and (dP < 0 or dJ < 0)) or (dP == 0 and dJ == 0 and free[q]) for (q, dP, dJ, pf) in perms):
                gate_white_wrong += 1
    nfree = sum(free)
    return tuple(w), n, nfree, bad_black, bad_white, unranked, gate_black_none, gate_white_wrong

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, free=0, bulkBlack_viol=0, bulkWhite_viol=0, unranked=0, gate_black_none=0, gate_white_wrong=0)
    words_bulk_bad = 0
    with Pool(12) as pool:
        for w, n, nf, bb, bw, un, gb, gw in pool.imap_unordered(run, ws):
            tot["classes"] += n
            tot["free"] += nf
            tot["bulkBlack_viol"] += bb
            tot["bulkWhite_viol"] += bw
            tot["unranked"] += un
            tot["gate_black_none"] += gb
            tot["gate_white_wrong"] += gw
            words_bulk_bad += (bb + bw + un) > 0
    print("TOTAL", tot, "words_with_bulk_violation", words_bulk_bad, flush=True)
