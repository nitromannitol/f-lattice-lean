"""Task 34 (ii): the e-policy with its prescribed inputs anchored in our chart.
Anchor: the archive core H0=(1,0), V0=(0,0), H_(d-1)-U=(0,-1), V_(-1)=(1,-1) lies in boundary classes of E; its E-
representatives are the exceptional classes. H-type classes (outward north neighbour) number d; V-type (outward west,
not north) number L. Prescribed input (direction), by ALL_SLOPE addendum, with eta:
  H-type: east (even), north (odd);  V-type: eta*east (even), -eta*north (odd);
  exceptional: H0 -> -eta*north, V0 -> east, H_(d-1)-U -> north, V_(-1) -> eta*east.
Kept sets: black both; non-free white: slip-permitted inputs (D_eta(a) <= D_eta(c)), the chosen one is among them;
free port: the prescribed input only.
Tests: bulk P,J at non-free kept edges (black: both; white: some slip input weak); same-level attractor; endpoint
certificate at each port's prescribed input; same-level port digraph acyclic."""
import sys
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, words
from arcs_check import e_rep
from bulk_dag import has_cycle

CORE = {"H0": (1, 0), "V0": (0, 0), "Hl": (0, -1), "Vl": (1, -1)}

def outward(fr, y):
    return [nm for nm, d in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
            if not fr.inE((y[0] + d[0], y[1] + d[1]))]

def run(args):
    w, eta = args
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm_S3, tg, K, V = systems["S3"]
    F, _ = pl.standard(tuple(w))
    N, Dd = pl.parents(w)[0]
    sig = (eta * 2 * fr.eps * Dd, eta * 2 * fr.eps * N)
    Dslip = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    P = cut_on(F, w, 1, 0, 1)
    J = cut_on(F, w, 0, 1, eta)
    det, S0 = re_.cover_sites(K, V)
    core_rep = {k: e_rep(fr, c) for k, c in CORE.items()}
    exc = {core_rep["H0"]: (0, -eta), core_rep["V0"]: (1, 0), core_rep["Hl"]: (0, 1), core_rep["Vl"]: (eta, 0)}
    info = {}
    H = V_ = 0
    for r in S0:
        y = e_rep(fr, r)
        tau = (r[0] - y[0], r[1] - y[1])
        out = outward(fr, y)
        port = len(out) > 0
        pres = None
        if port:
            if y in exc:
                pres = exc[y]
            elif "N" in out:
                pres = (1, 0) if (y[0] + y[1]) % 2 == 0 else (0, 1)
            else:
                pres = (eta, 0) if (y[0] + y[1]) % 2 == 0 else (0, -eta)
            if "N" in out:
                H += 1
            else:
                V_ += 1
        info[r] = (y, tau, port, pres)
    def e_perm(c, a):
        y, tau, port, pres = info[c]
        if lap(c) == -1:
            return True
        if port:
            a_loc = (a[0] - tau[0], a[1] - tau[1])
            return (a_loc[0] - y[0], a_loc[1] - y[1]) == pres
        return Dslip(a) <= Dslip(c)
    n, S0b, gP, lapv, eP, _ = build(K, V, lap, e_perm, P)
    _, _, gJ, _, eJ, _ = build(K, V, lap, e_perm, J)
    E = [[(q, gP[q] + wP - gP[p], gJ[q] + wJ - gJ[p], pf) for (q, wP, pf), (q2, wJ, pf2) in zip(eP[p], eJ[p])] for p in range(n)]
    port = [info[r][2] for r in S0b]
    viol_bP = viol_bJ = 0
    nonfree_bad_white = 0
    for p in range(n):
        if port[p]:
            continue
        if lapv[p] == -1:
            for (q, dP, dJ, pf) in E[p]:
                viol_bP += dP > 0
                viol_bJ += dJ > 0
        else:
            ok = any(pf and dP <= 0 and dJ <= 0 for (q, dP, dJ, pf) in E[p])
            nonfree_bad_white += (not ok)
    ranked = list(port)
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
    unranked = sum(1 for p in range(n) if not ranked[p])
    cert_fail = []
    for p in range(n):
        if not port[p]:
            continue
        kept = [(q, dP, dJ) for (q, dP, dJ, pf) in E[p] if pf]
        ok = any(dP <= 0 and dJ <= 0 and (dP < 0 or dJ < 0 or (port[q] and dP == 0 and dJ == 0)) for (q, dP, dJ) in kept)
        if not ok:
            cert_fail.append(S0b[p])
    same_free = {p: [q for (q, dP, dJ, pf) in E[p] if pf and dP == 0 and dJ == 0 and port[q]] for p in range(n) if port[p]}
    cyc = has_cycle(list(same_free), same_free)
    return tuple(w), eta, n, sum(port), H, V_, viol_bP, viol_bJ, nonfree_bad_white, unranked, len(cert_fail), (cert_fail[0] if cert_fail else None), cyc

if __name__ == "__main__":
    ws = list(words(4))
    eta = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    tot = dict(classes=0, ports=0, H=0, V=0, bP_black=0, bJ_black=0, bad_white=0, unranked=0, cert_fail=0, words_cycle=0)
    fails = []
    with Pool(12) as pool:
        for w, e, n, np_, H, V_, bP, bJ, bw, un, cf, ex, cyc in pool.imap_unordered(run, [(w, eta) for w in ws]):
            tot["classes"] += n; tot["ports"] += np_; tot["H"] += H; tot["V"] += V_
            tot["bP_black"] += bP; tot["bJ_black"] += bJ; tot["bad_white"] += bw
            tot["unranked"] += un; tot["cert_fail"] += cf; tot["words_cycle"] += cyc
            if cf or un or bP or bJ or bw or cyc:
                fails.append((len(w), w, cf, ex))
    print("ETA", eta, "TOTAL", tot, flush=True)
    print("WORDS_WITH_FAILURES", len(fails), flush=True)
    for f in sorted(fails)[:5]:
        print("WORD", f[1], "cert_fail", f[2], "smallest_failing_port", f[3], flush=True)
