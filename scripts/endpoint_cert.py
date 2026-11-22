"""Task 32 (f): the endpoint certificate of WEIGHTED line 3, as a local condition on classes.
Free set = the E boundary ports (archive: 'the whole finite free set on B', 2d+n ports per word; arcs_check.py).
For a free class z and a kept input a of z (S3 kept = slip permits): z satisfies the certificate at a if
  dP <= 0, dJ <= 0, and (dP < 0 or dJ < 0 or (a is free and dP = dJ = 0)).
Existential form: some kept input of z satisfies it (the prescribed input may be chosen).
Also: the same-level free digraph (edges z -> a, a free, dP = dJ = 0) must be acyclic (finite elimination order).
Also: P-monotonicity of kept edges from NON-boundary classes (is the archive's bulk input true for these kept edges?)."""
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, words
from arcs_check import e_rep
from bulk_dag import has_cycle

def run(w):
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    frm = pl.Frame(w)
    F, _ = pl.standard(tuple(w))
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, 1)
    n, S0, gP, lapv, eP, _ = build(K, V, lap, perm, P)
    _, _, gJ, _, eJ, _ = build(K, V, lap, perm, J)
    E = [[(q, gP[q] + wP - gP[p], gJ[q] + wJ - gJ[p], pf) for (q, wP, pf), (q2, wJ, pf2) in zip(eP[p], eJ[p])] for p in range(n)]
    bnd = set()
    for p, z in enumerate(S0):
        y = e_rep(frm, z)
        nbrs = [(y[0] + 1, y[1]), (y[0] - 1, y[1]), (y[0], y[1] + 1), (y[0], y[1] - 1)]
        if any(not frm.inE(q) for q in nbrs):
            bnd.add(p)
    cert_fail = []
    for p in bnd:
        ok = False
        for (q, dP, dJ, pf) in E[p]:
            if not pf:
                continue
            if dP <= 0 and dJ <= 0 and (dP < 0 or dJ < 0 or (q in bnd and dP == 0 and dJ == 0)):
                ok = True
                break
        if not ok:
            cert_fail.append(S0[p])
    same = {p: [q for (q, dP, dJ, pf) in E[p] if pf and dP == 0 and dJ == 0 and q in bnd] for p in bnd}
    dag_cycle = has_cycle(list(bnd), {p: same[p] for p in bnd})
    # archive's bulk input: kept edges from NON-boundary classes must not raise P or J
    interior_viol_P = sum(1 for p in range(n) if p not in bnd for (q, dP, dJ, pf) in E[p] if pf and dP > 0)
    interior_viol_J = sum(1 for p in range(n) if p not in bnd for (q, dP, dJ, pf) in E[p] if pf and dJ > 0)
    return tuple(w), len(bnd), len(cert_fail), dag_cycle, interior_viol_P, interior_viol_J, cert_fail[:3]

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(ports=0, cert_fail=0, words_cert_fail=0, words_dag_cycle=0, interior_P_viol=0, interior_J_viol=0)
    rows = []
    with Pool(12) as pool:
        for w, nb, cf, dc, ivp, ivj, ex in pool.imap_unordered(run, ws):
            tot["ports"] += nb; tot["cert_fail"] += cf
            tot["words_cert_fail"] += cf > 0
            tot["words_dag_cycle"] += dc
            tot["interior_P_viol"] += ivp; tot["interior_J_viol"] += ivj
            rows.append((w, nb, cf, dc, ivp, ivj, ex))
    print("TOTAL", tot, flush=True)
    for r in sorted(rows, key=lambda r: (len(r[0]), r[0]))[:6]:
        print("WORD", r[0], "ports", r[1], "cert_fail", r[2], "dag_cycle", r[3], "interior_P", r[4], "interior_J", r[5], "ex", r[6], flush=True)
