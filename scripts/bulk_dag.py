"""Archive inputs for S3 on all 116 words, with the minimal free set forced by bulk monotonicity of P:
  free := { classes z : some permitted input a of z has P(a) > P(z) }   (deck invariant; P, J differences are invariant)
  (B-DAG) the digraph on NON-free classes, with an edge z -> rep(a) for each permitted input a of z, is acyclic
          (an ℕ-valued bulk order decreasing along allowed edges exists iff no infinite allowed path, i.e. no cycle)
  (ENDPOINT, local necessary form) every free class z has a permitted input with dP <= 0, dJ <= 0, not both 0 (strict),
          or a permitted input that is free with dP = dJ = 0 (same pair, to be ordered by freeOrder);
          the same-pair free edges must be acyclic (finite elimination order)."""
import sys
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, words

def has_cycle(nodes, adj):
    color = {v: 0 for v in nodes}
    for s in nodes:
        if color[s]:
            continue
        stack = [(s, iter(adj[s]))]
        color[s] = 1
        while stack:
            v, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                color[v] = 2
                stack.pop()
            elif color[nxt] == 1:
                return True
            elif color[nxt] == 0:
                color[nxt] = 1
                stack.append((nxt, iter(adj[nxt])))
    return False

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
        lst = []
        for (q, wP, pf), (q2, wJ, pf2) in zip(eP[p], eJ[p]):
            assert q == q2 and pf == pf2
            lst.append((q, gP[q] + wP - gP[p], gJ[q] + wJ - gJ[p], pf))
        E.append(lst)
    free = [any(pf and dP > 0 for (q, dP, dJ, pf) in E[p]) for p in range(n)]
    nonfree = [p for p in range(n) if not free[p]]
    # monotonicity of J on non-free centres and of P (by construction)
    jviol = sum(1 for p in nonfree for (q, dP, dJ, pf) in E[p] if pf and dJ > 0)
    adj = {p: [q for (q, dP, dJ, pf) in E[p] if pf and not free[q]] for p in nonfree}
    cyc = has_cycle(nonfree, adj)
    no_cert = 0
    same_cycle = False
    same = {}
    for p in range(n):
        if not free[p]:
            continue
        strict = any(pf and dP <= 0 and dJ <= 0 and (dP < 0 or dJ < 0) for (q, dP, dJ, pf) in E[p])
        sm = [q for (q, dP, dJ, pf) in E[p] if pf and dP == 0 and dJ == 0 and free[q]]
        if not strict and not sm:
            no_cert += 1
        same[p] = sm
    if same:
        same_cycle = has_cycle(list(same.keys()), {p: [q for q in same[p] if q in same] for p in same})
    return tuple(w), n, sum(free), jviol, cyc, no_cert, same_cycle

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, free=0, jviol=0, dag_cycle_words=0, no_cert=0, same_cycle_words=0)
    with Pool(12) as pool:
        for w, n, nf, jv, cyc, nc, sc in pool.imap_unordered(run, ws):
            tot["classes"] += n
            tot["free"] += nf
            tot["jviol"] += jv
            tot["dag_cycle_words"] += cyc
            tot["no_cert"] += nc
            tot["same_cycle_words"] += sc
            if cyc or nc or sc or jv:
                print("WORD", w, "n", n, "free", nf, "jviol", jv, "dagcycle", cyc, "no_cert", nc, "samecycle", sc, flush=True)
    print("TOTAL", tot, flush=True)
