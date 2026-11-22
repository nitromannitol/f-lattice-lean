"""I3A grades: the conjugate frame's cutGrade on G = standard(conjWord w), transported by the quarter turn
q(x) = (-x2, x1 - 1) to Fp, i.e. grade(x) = cutGrade_G(conj)(q(x)); A, C in {1,2}, eta in {+1,-1}.
Same exact quotient test (value iteration on the odd-parent deck of I3A), all 116 proper words."""
import sys, time
from multiprocessing import Pool
import numpy as np
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, check_deck, words
from value_iter import value_iter
import random

def grades_for(w):
    conj = tuple(pl.swap(pl.odd_birth_prefix(list(w))))
    G, _ = pl.standard(conj)
    out = {}
    for A in (1, 2):
        for C in (1, 2):
            for eta in (1, -1):
                Kc = cut_on(G, list(conj), A, C, eta)
                out[(A, C, eta)] = (lambda Kc: (lambda x: Kc((-x[1], x[0] - 1))))(Kc)
    return out

def run(w):
    w = list(w)
    systems, _ = re_.systems_for(w)
    lap, perm, tgrade, K, V = systems["I3A"]
    rng = random.Random(3)
    res = {}
    for key, grade in grades_for(w).items():
        n, S0, g, lapv, edges, tau_checks = build(K, V, lap, perm, grade)
        inv = check_deck(lap, perm, grade, S0, tau_checks, rng)
        r, fixed, it = value_iter(n, g, lapv, edges, 1000 * n + 10000)
        res[key] = dict(n=n, esc=int(np.sum(r <= -1)), non=(int(np.sum(r == 0)) if fixed else 0),
                        undec=(0 if fixed else int(np.sum(r == 0))), inv=inv, fixed=fixed)
    return tuple(w), res

if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    t0 = time.time()
    ws = list(words(maxlen))
    keys = [(A, C, e) for A in (1, 2) for C in (1, 2) for e in (1, -1)]
    agg = {k: dict(words_non=0, non=0, undec=0, inv_words=0, esc=0) for k in keys}
    with Pool(12) as pool:
        for w, res in pool.imap_unordered(run, ws):
            for k in keys:
                x = res[k]
                a = agg[k]
                a["words_non"] += (x["non"] > 0)
                a["non"] += x["non"]
                a["undec"] += x["undec"]
                a["esc"] += x["esc"]
                a["inv_words"] += (x["inv"] > 0)
            print("WORD", w, " ".join(f"{k[0]}{k[1]}{'+' if k[2]==1 else '-'}:non{res[k]['non']}/und{res[k]['undec']}/inv{res[k]['inv']}" for k in keys), flush=True)
    for k in keys:
        print("TOTAL I3A grade (A,C,eta)=", k, agg[k], flush=True)
    print("SEC", round(time.time() - t0), flush=True)
