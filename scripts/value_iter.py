"""Lead's test: value iteration on the finite deck quotient.
r(z) = h(z) - grade(z), h = lowest level a strategy tree from z guarantees. r is deck-periodic and r <= 0.
  r_{n+1}(z) = min(0, op(r_n(a) + D_a, r_n(b) + D_b)),  op = max at charge -1 (both inputs permitted), min at charge 0
  over permitted inputs (+BIG if none), D_a = grade(a) - grade(z).
A class escapes iff r_n(z) <= -1 for some n (finite certificate). If the iteration reaches a fixed point, classes with
r = 0 do not escape (certificate). Otherwise classes with r = 0 are undecided at the iteration limit."""
import sys, time
import numpy as np
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, check_deck, words
import random

BIG = 10 ** 9


def value_iter(n, g, lapv, edges, maxit):
    q1 = np.array([edges[p][0][0] for p in range(n)], dtype=np.int64)
    q2 = np.array([edges[p][1][0] for p in range(n)], dtype=np.int64)
    w1 = np.array([edges[p][0][1] for p in range(n)], dtype=np.int64)
    w2 = np.array([edges[p][1][1] for p in range(n)], dtype=np.int64)
    p1 = np.array([bool(edges[p][0][2]) for p in range(n)])
    p2 = np.array([bool(edges[p][1][2]) for p in range(n)])
    gg = np.array(g, dtype=np.int64)
    lap = np.array(lapv, dtype=np.int64)
    D1 = gg[q1] + w1 - gg          # grade(a) - grade(z) for the first input a = rep(q1) + tau
    D2 = gg[q2] + w2 - gg
    r = np.zeros(n, dtype=np.int64)
    fixed = False
    it = 0
    for it in range(1, maxit + 1):
        v1 = np.where(p1, r[q1] + D1, BIG)
        v2 = np.where(p2, r[q2] + D2, BIG)
        cand = np.where(lap == -1, np.maximum(v1, v2), np.minimum(v1, v2))
        new = np.minimum(cand, 0)
        if np.array_equal(new, r):
            fixed = True
            break
        r = new
        if not np.any(r == 0):
            break   # every class has escaped: the escape certificates are complete
    return r, fixed, it


def run_word(w, maxit_factor=1):
    w = list(w)
    systems, fr = re_.systems_for(w)
    Fp, Xi, off = pl.model(w)
    F, _ = pl.standard(tuple(w))
    rng = random.Random(7)
    out = {}
    for sname in ("S3", "I3A", "I3C"):
        lap, perm, tgrade, K, V = systems[sname]
        field = F if sname == "S3" else Fp
        grades = {"K+1": cut_on(field, w, 1, 1, 1), "K-1": cut_on(field, w, 1, 1, -1), "t": tgrade}
        for gname, grade in grades.items():
            n, S0, g, lapv, edges, tau_checks = build(K, V, lap, perm, grade)
            inv = check_deck(lap, perm, grade, S0, tau_checks, rng)
            r, fixed, it = value_iter(n, g, lapv, edges, maxit_factor * n + 200)
            esc = int(np.sum(r <= -1))
            zero = int(np.sum(r == 0))
            out[(sname, gname)] = dict(n=n, esc=esc, nonesc=(zero if fixed else 0), undecided=(0 if fixed else zero),
                                       fixed=fixed, iters=it, inv=inv,
                                       sample=[S0[p] for p in np.nonzero(r == 0)[0][:3]])
    return tuple(w), out


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    which = sys.argv[2] if len(sys.argv) > 2 else "all"
    ws = list(words(maxlen)) if which == "all" else [tuple(int(c) for c in x.split(",")) for x in which.split(";")]
    t0 = time.time()
    combos = [(s, g) for s in ("S3", "I3A", "I3C") for g in ("K+1", "K-1", "t")]
    agg = {c: dict(words_nonesc=0, nonesc=0, words_undec=0, undec=0, not_fixed=0, esc=0) for c in combos}
    inv_fail = 0
    with Pool(12) as pool:
        for w, res in pool.imap_unordered(run_word, ws):
            if any(res[c]["inv"] > 0 for c in combos):
                inv_fail += 1
            parts = []
            for c in combos:
                x = res[c]
                a = agg[c]
                a["esc"] += x["esc"]
                a["words_nonesc"] += (x["nonesc"] > 0)
                a["nonesc"] += x["nonesc"]
                a["words_undec"] += (x["undecided"] > 0)
                a["undec"] += x["undecided"]
                a["not_fixed"] += (not x["fixed"])
                parts.append(f"{c[0]}/{c[1]}:esc{x['esc']},non{x['nonesc']},und{x['undecided']},it{x['iters']}")
            print("WORD", w, " ".join(parts), flush=True)
    for c in combos:
        print("TOTAL", c, agg[c], flush=True)
    print("INVARIANCE_FAIL_WORDS", inv_fail, "sec", round(time.time() - t0), flush=True)
