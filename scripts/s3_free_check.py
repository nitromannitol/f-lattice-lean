"""Task 58 numerics: the free H/V boundary of Q1 with its prescribed directions, and the acyclicity test (words <= 4).

Free boundary (representatives in the closed polygon E of the child frame of the word):
  H-trace  = { z in E : z-(0,1) not in E, t(z) in the H spectrum }, ordered by x:  H_0, ..., H_{d-1}  (d sites)
             H spectrum: t = 2,4,...,L-2 (even) and n, n+2, ..., d (odd).
  V-cut    = { z in E : z-(1,0) not in E, s(z) in the V spectrum }, ordered by y:  V_0, ..., V_{L-1}  (L sites)
             V spectrum: s = 0,2,...,2n (even) and 2-d+n, ..., L-2 (odd).
  (checked: counts d and L on all words of length <= 3; H_0=(1,0), H_{d-1}=(d,n-1), V_0=(0,0).)
Prescribed kept input at a free representative (horizontal sign minus, vertical sign eta):
  internal H (1<=j<=d-2): east at even (= incomingPos), north at odd (= incomingPos);
  H_0: -eta north; H_{d-1}: north;
  internal V (1<=j<=L-2): eta east at even, -eta north at odd;
  V_0: east; V_{L-1}: eta east.
  (east = z+(1,0), north = z+(0,1), west = z-(1,0), south = z-(0,1); for eta=-1, east is replaced by west, etc.)
Kept graph on the representatives: prescribed inputs at free whites; both inputs at blacks; at the other whites an attractor
witness (rank from the free base: a white is ranked when it has a permitted strict-drop input, or a permitted equal-pair input
of smaller rank; a black when all its equal-pair inputs are ranked).
Checks: (a) every prescribed edge is permitted (slip increment <= 0) and weakly lower in (P, J_eta);
        (b) the equal-pair kept graph is acyclic on the representatives (Kahn); a cycle is reported when found.
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import cut_on, words

EAST, NORTH, WEST, SOUTH = (1, 0), (0, 1), (-1, 0), (0, -1)


def run(args):
    w, eta = args
    w = list(w)
    F, _ = pl.standard(tuple(w))
    fr = oc.frame(w)
    N, D, n, d, T, eps = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"], fr["eps"]
    L = n + d
    P = cut_on(F, w, 1, 0, 1)
    # Task 72 Q13: the grading J_eta = ceil(D_eta/2) and the raw slip D_eta(z) = F(z) - F(z + eta*sigma) use the sign eta.
    J = cut_on(F, w, 0, 1, eta)
    short = (2 * eps * D, 2 * eps * N)
    U, V = (d, n), (n - d, n + d)

    def D1(z):
        return F(z) - F((z[0] + eta * short[0], z[1] + eta * short[1]))

    def permitted(c, i):
        return D1(i) - D1(c) <= 0

    def inE(z):
        return oc.in_polygon(z, fr)

    def tg(z):
        return n * z[0] - d * z[1]

    def sg(z):
        return (d + n) * z[0] + (d - n) * z[1]

    def reduce(z):
        even = oc.even_site(z)
        tlo = 2 - T if even else n - T
        slo = 0 if even else 2 - d + n
        b = (tg(z) - tlo) // T
        z1 = (z[0] + b * V[0], z[1] + b * V[1])
        a = -((sg(z1) - slo) // T)
        return (z1[0] + a * U[0], z1[1] + a * U[1])

    x0, x1, y0, y1 = oc.window(fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    repset = set(reps)
    Hspec = set(range(2, L - 1, 2)) | set(range(n, d + 1, 2))
    Vspec = set(range(0, 2 * n + 1, 2)) | set(range(2 - d + n, L - 1, 2))
    Hb = sorted((z for z in reps if not inE((z[0], z[1] - 1)) and tg(z) in Hspec), key=lambda z: z[0])
    Vb = sorted((z for z in reps if not inE((z[0] - 1, z[1])) and sg(z) in Vspec), key=lambda z: z[1])
    free_idx = {}
    for j, z in enumerate(Hb):
        free_idx[z] = ("H", j)
    for k, z in enumerate(Vb):
        assert z not in free_idx, (w, z)
        free_idx[z] = ("V", k)
    stats = defaultdict(int)
    stats["H_count_ok"] += len(Hb) == d
    stats["V_count_ok"] += len(Vb) == L

    def ins(z):
        return oc.incoming_neg(z), oc.incoming_pos(z)

    # prescribed input at a free representative
    presc = {}
    for z, (kind, j) in free_idx.items():
        if kind == "H":
            if j == 0:
                # -eta north: eta=1 -> south, eta=-1 -> north
                dirv = SOUTH if eta == 1 else NORTH
            elif j == d - 1:
                dirv = NORTH
            else:
                dirv = EAST if oc.even_site(z) else NORTH
        else:
            if j == 0:
                dirv = EAST
            elif j == L - 1:
                dirv = EAST if eta == 1 else WEST
            else:
                if oc.even_site(z):
                    dirv = EAST if eta == 1 else WEST
                else:
                    dirv = SOUTH if eta == 1 else NORTH
        i = (z[0] + dirv[0], z[1] + dirv[1])
        assert i in ins(z), (w, z, kind, j, i)
        presc[z] = i
    # (a) prescribed edges: permitted and weakly lower
    for z, i in presc.items():
        stats["presc"] += 1
        if not permitted(z, i):
            stats["presc_not_permitted"] += 1
        dP = P(i) - P(z)
        dJ = J(i) - J(z)
        if not (dP <= 0 and dJ <= 0):
            stats["presc_not_lower"] += 1
        if dP == 0 and dJ == 0:
            stats["presc_equal_pair"] += 1
    # attractor ranks on representatives with the free base
    info = {}
    for r in reps:
        lv = pl.lap(F, r)
        ii = [oc.incoming_neg(r), oc.incoming_pos(r)]
        info[r] = (lv, [(i, P(i) - P(r), J(i) - J(r), permitted(r, i), reduce(i)) for i in ii])
    rank = {r: (0 if r in free_idx else None) for r in reps}
    step = 0
    while True:
        step += 1
        new = []
        for p in reps:
            if rank[p] is not None:
                continue
            lv, perms = info[p]
            perms = [(q, dP, dJ) for (_, dP, dJ, pf, q) in perms if pf]
            same = [q for (q, dP, dJ) in perms if dP == 0 and dJ == 0]
            if lv == -1:
                ok = all(rank[q] is not None for q in same)
            else:
                lower = any(dP <= 0 and dJ <= 0 and (dP < 0 or dJ < 0) for (q, dP, dJ) in perms)
                ok = lower or any(rank[q] is not None for q in same)
            if ok:
                new.append(p)
        if not new:
            break
        for p in new:
            rank[p] = step
    stats["unranked_nonfree"] += sum(1 for r in reps if r not in free_idx and rank[r] is None)
    # kept graph
    graph = {r: [] for r in reps}
    kept_edge = {}
    for r in reps:
        lv, perms = info[r]
        if r in free_idx:
            i = presc[r]
            q = reduce(i)
            dP, dJ = P(i) - P(r), J(i) - J(r)
            kept_edge[r] = [(i, q, dP, dJ)]
        elif lv == -1:
            kept_edge[r] = [(i, q, dP, dJ) for (i, dP, dJ, pf, q) in perms]
        else:
            cand = [(i, q, dP, dJ) for (i, dP, dJ, pf, q) in perms if pf and dP <= 0 and dJ <= 0]
            if not cand:
                stats["white_no_witness"] += 1
                kept_edge[r] = []
                continue
            strict = [c for c in cand if c[2] < 0 or c[3] < 0]
            if strict:
                kept_edge[r] = [strict[0]]
            else:
                ranked = [c for c in cand if rank[c[1]] is not None and rank[c[1]] < rank[r]]
                kept_edge[r] = [ranked[0]] if ranked else [cand[0]]
                stats["white_equal_witness"] += 1
        for (i, q, dP, dJ) in kept_edge[r]:
            if dP == 0 and dJ == 0:
                graph[r].append(q)
    # CanonicalPolicy checks (task 59 step 3): quota, permitted and weakly lower kept edges, free whites, Kahn levels.
    for r in reps:
        lapv = info[r][0]
        for (i, q, dP, dJ) in kept_edge[r]:
            stats["kept_total"] += 1
            if not permitted(r, i):
                stats["kept_not_permitted"] += 1
            if not (dP <= 0 and dJ <= 0):
                stats["kept_not_lower"] += 1
        nk = len(kept_edge[r])
        if lapv == -1:
            stats["black_kept_two"] += (nk == 2)
            stats["black_kept_not_two"] += (nk != 2)
        else:
            stats["white_kept_one"] += (nk == 1)
            stats["white_kept_not_one"] += (nk != 1)
        if r in free_idx:
            stats["free_sites"] += 1
            stats["free_black"] += (lapv == -1)
            stats["free_kept_not_prescribed"] += (kept_edge[r][0][0] != presc[r] or nk != 1)
    # Kahn levels on the equal-pair kept graph: level = 1 + max level of kept successors (sinks at 0)
    outdeg = {r: len(graph[r]) for r in reps}
    preds = defaultdict(list)
    for r in reps:
        for t in graph[r]:
            preds[t].append(r)
    level = {}
    ready = [r for r in reps if outdeg[r] == 0]
    for r in ready:
        level[r] = 0
    k = 0
    while k < len(ready):
        t = ready[k]
        k += 1
        for r in preds[t]:
            outdeg[r] -= 1
            if outdeg[r] == 0:
                level[r] = 1 + max(level[x] for x in graph[r])
                ready.append(r)
    stats["levelled"] = len(level)
    stats["level_violations"] = sum(1 for r in reps for t in graph[r]
                                     if r in level and t in level and not level[t] < level[r])
    # (b) acyclicity (Kahn) on equal-pair kept edges
    indeg = defaultdict(int)
    for r in reps:
        for s in graph[r]:
            indeg[s] += 1
    queue = [r for r in reps if indeg[r] == 0]
    seen = 0
    while queue:
        r = queue.pop()
        seen += 1
        for s in graph[r]:
            indeg[s] -= 1
            if indeg[s] == 0:
                queue.append(s)
    stats["cycle_nodes"] = len(reps) - seen
    cyc = None
    if seen < len(reps):
        # smallest cycle by DFS from a leftover node
        left = [r for r in reps if indeg[r] > 0]
        start = left[0]
        path, pos = [start], {start: 0}
        cur = start
        while True:
            nxt = [s for s in graph[cur] if indeg[s] > 0]
            if not nxt:
                break
            cur = nxt[0]
            if cur in pos:
                cyc = path[pos[cur]:]
                break
            pos[cur] = len(path)
            path.append(cur)
    return tuple(w), eta, dict(stats), len(reps), len(Hb), len(Vb), cyc


if __name__ == "__main__":
    import sys
    ws = list(words(4))
    etas = [1, -1] if "--both" in sys.argv else [1]
    jobs = [(w, e) for w in ws for e in etas]
    tot = defaultdict(int)
    bad = []
    with Pool(12) as pool:
        for w, e, st, nreps, nh, nv, cyc in pool.imap_unordered(run, jobs):
            for k, v in st.items():
                tot[k] += v
            tot["reps"] += nreps
            if st.get("presc_not_permitted") or st.get("presc_not_lower") or st.get("cycle_nodes") or st.get("white_no_witness") or st.get("unranked_nonfree"):
                bad.append((w, e, {k: v for k, v in st.items() if v}, cyc))
    print("TOTAL", dict(tot), flush=True)
    print("BAD", len(bad), flush=True)
    for b in sorted(bad, key=lambda t: (len(t[0]), t[0]))[:8]:
        print("  ", b[0], "eta", b[1], b[2], "cycle", b[3], flush=True)
