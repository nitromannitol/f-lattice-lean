"""Exact escape test on the finite deck quotient (no radius).

For a system (field, permits, laplacian, deck K,V) and a grade g with deck increments w(tau) = g(z+tau) - g(z):
escape(z, m) (escape from level m) is the least fixpoint of
  base:       g(z) < m
  lap -1:     both permitted inputs escape at level m
  lap  0:     one permitted input escapes at level m
Escape at level m is upward closed in m, so T(r) = inf{m : escape(r, m)} on the quotient reps r satisfies
  T(r) = min( g(r)+1 , op over the two neighbours a = r'+tau of (T(r') + w) ),
  op = max over both (lap -1, both permitted; +inf otherwise) / min over permitted (lap 0; +inf if none).
T is the least fixpoint, computed from +inf by a worklist.  A node updated more than CAP times has a negative cycle
and is set to -inf (escape at every level).  A cover site s escapes iff T(s) <= g(s).
mode 'relaxed' replaces the lap -1 AND by an OR (min over permitted inputs): the reachability-with-negative-cycles
test of the lead's rule, for comparison.
"""
import sys, math, time, random
from collections import deque
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_

INF = math.inf


def cut_on(field, w, A, C, eta):
    fr = pl.Frame(list(w))
    (N, D), _ = pl.parents(list(w))[0], None
    eps = fr.eps
    par = (eps * (N - D), eps * (N + D))
    short = (2 * eps * D, 2 * eps * N)

    def K(z):
        price = field(z) - field((z[0] - par[0], z[1] - par[1])) - eps * (N * z[0] - D * z[1])
        s = field(z) - field((z[0] + eta * short[0], z[1] + eta * short[1]))
        return A * price + C * ((s + 1) // 2)
    return K


def build(K, V, lap, perm, grade):
    det, S0 = re_.cover_sites(K, V)
    D = abs(det)

    def key(z):
        return ((V[1] * z[0] - V[0] * z[1]) % D, (K[0] * z[1] - K[1] * z[0]) % D)
    index = {}
    for i, r in enumerate(S0):
        k = key(r)
        assert k not in index, "cover not one site per class"
        index[k] = i
    assert len(index) == D == len(S0)
    n = len(S0)
    g = [grade(r) for r in S0]
    lapv = [lap(r) for r in S0]
    assert all(l in (-1, 0) for l in lapv), "non-binary laplacian on cover"
    edges, tau_checks = [], []
    for p, r in enumerate(S0):
        es = []
        for a in pl.neighbours(r):
            q = index[key(a)]
            tau = (a[0] - S0[q][0], a[1] - S0[q][1])
            w = grade(a) - g[q]
            es.append((q, w, perm(r, a)))
            tau_checks.append((r, tau, w))
        edges.append(es)
    return n, S0, g, lapv, edges, tau_checks


def check_deck(lap, perm, grade, S0, tau_checks, rng):
    """Sampled check: grade increment, laplacian and permits are invariant under the deck translation of each edge."""
    bad = 0
    for (r, tau, w) in tau_checks:
        for x in (r, S0[rng.randrange(len(S0))]):
            xt = (x[0] + tau[0], x[1] + tau[1])
            if grade(xt) - grade(x) != w or lap(xt) != lap(x):
                bad += 1
            for y in pl.neighbours(x):
                yt = (y[0] + tau[0], y[1] + tau[1])
                if perm(xt, yt) != perm(x, y):
                    bad += 1
    return bad


def quotient_T(n, g, lapv, edges, exact=True):
    pred = [[] for _ in range(n)]
    for p in range(n):
        for (q, w, pf) in edges[p]:
            pred[q].append(p)
    T = [INF] * n
    cnt = [0] * n
    CAP = 3 * n + 20
    dq = deque(range(n))
    inq = [True] * n
    capped = 0
    while dq:
        p = dq.popleft()
        inq[p] = False
        (q1, w1, p1), (q2, w2, p2) = edges[p]
        c1 = T[q1] + w1
        c2 = T[q2] + w2
        cands = [g[p] + 1]
        if lapv[p] == -1 and exact:
            cands.append(max(c1, c2) if (p1 and p2) else INF)
        else:
            opts = [c for c, pf in ((c1, p1), (c2, p2)) if pf]
            cands.append(min(opts) if opts else INF)
        new = min(cands)
        if new < T[p]:
            cnt[p] += 1
            if cnt[p] > CAP and new != -INF:
                new = -INF
                capped += 1
            T[p] = new
            for pp in pred[p]:
                if not inq[pp]:
                    inq[pp] = True
                    dq.append(pp)
    return T, capped


def run_word(w, check=True):
    w = list(w)
    systems, fr = re_.systems_for(w)
    Fp, Xi, off = pl.model(w)
    F, _ = pl.standard(tuple(w))
    rng = random.Random(7)
    out = {}
    for sname in ("S3", "I3A", "I3C"):
        lap, perm, tgrade, K, V = systems[sname] if False else re_.systems_for(w)[0][sname]
        field = F if sname == "S3" else Fp
        grades = {"K+1": cut_on(field, w, 1, 1, 1), "K-1": cut_on(field, w, 1, 1, -1), "t": tgrade}
        for gname, grade in grades.items():
            n, S0, g, lapv, edges, tau_checks = build(K, V, lap, perm, grade)
            bad_inv = check_deck(lap, perm, grade, S0, tau_checks, rng) if check else -1
            for mode in ("exact", "relaxed"):
                T, capped = quotient_T(n, g, lapv, edges, exact=(mode == "exact"))
                nonesc = [S0[p] for p in range(n) if not (T[p] <= g[p])]
                out[(sname, gname, mode)] = dict(n=n, nonesc=len(nonesc), capped=capped, sample=nonesc[:3], inv=bad_inv)
    return tuple(w), out


def words(maxlen):
    import itertools
    for Lw in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=Lw):
            if not all(x == 3 for x in w):
                yield w


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    which = sys.argv[2] if len(sys.argv) > 2 else "all"
    ws = list(words(maxlen)) if which == "all" else [tuple(int(c) for c in x.split(",")) for x in which.split(";")]
    t0 = time.time()
    combos = [(s, g, m) for s in ("S3", "I3A", "I3C") for g in ("K+1", "K-1", "t") for m in ("exact", "relaxed")]
    tot = {c: [0, 0, 0] for c in combos}   # words with nonesc, total nonesc, capped
    inv_fail = 0
    with Pool(12) as pool:
        for w, res in pool.imap_unordered(run_word, ws):
            for c in combos:
                r = res[c]
                tot[c][0] += (r["nonesc"] > 0)
                tot[c][1] += r["nonesc"]
                tot[c][2] += r["capped"]
                if r["inv"] > 0:
                    inv_fail += 1
            line = " ".join(f"{s}/{g}/{m}:{res[(s,g,m)]['nonesc']}" for (s, g, m) in combos)
            print("WORD", w, line, "inv_fail" if any(res[c]["inv"] > 0 for c in combos) else "", flush=True)
    for c in combos:
        print("TOTAL", c, "words_bad", tot[c][0], "nonesc_sites", tot[c][1], "capped", tot[c][2], flush=True)
    print("INVARIANCE_FAILS", inv_fail, "sec", round(time.time() - t0), flush=True)
