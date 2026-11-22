"""S3 with matched signs: the slip permits built from the same short step as the grade.
eta=+1: permits slipIncrement(F, F(.+sigma)) <= 0, grade cutGrade F 1 1 1 (matched; the variant's pair).
eta=-1: permits slipIncrement(F, F(.-sigma)) <= 0, grade cutGrade F 1 1 (-1) (matched).
Also the mismatched pairs for comparison. Same exact quotient test, all 116 words."""
import sys, time, random
import numpy as np
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from exact_quotient import cut_on, build, check_deck, words
from value_iter import value_iter

def run(w):
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm_plus, tgrade, K, V = systems["S3"]
    F, _ = pl.standard(tuple(w))
    N, D = pl.parents(w)[0]
    sig = (2 * fr.eps * D, 2 * fr.eps * N)
    def slip_of(sign):
        s = (sign * sig[0], sign * sig[1])
        return lambda c, i: (F(i) - F((i[0] + s[0], i[1] + s[1]))) - (F(c) - F((c[0] + s[0], c[1] + s[1])))
    perm = {1: (lambda c, i: slip_of(1)(c, i) <= 0), -1: (lambda c, i: slip_of(-1)(c, i) <= 0)}
    grades = {1: cut_on(F, w, 1, 1, 1), -1: cut_on(F, w, 1, 1, -1)}
    rng = random.Random(5)
    res = {}
    for pe in (1, -1):
        for ge in (1, -1):
            n, S0, g, lapv, edges, tau = build(K, V, lap, perm[pe], grades[ge])
            inv = check_deck(lap, perm[pe], grades[ge], S0, tau, rng)
            r, fixed, it = value_iter(n, g, lapv, edges, 1000 * n + 10000)
            res[(pe, ge)] = dict(non=(int(np.sum(r == 0)) if fixed else 0), zero=int(np.sum(r == 0)), esc=int(np.sum(r <= -1)), inv=inv, fixed=fixed)
    return tuple(w), res

if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    t0 = time.time()
    ws = list(words(maxlen))
    keys = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
    agg = {k: dict(words_non=0, non=0, inv_words=0) for k in keys}
    with Pool(12) as pool:
        for w, res in pool.imap_unordered(run, ws):
            for k in keys:
                agg[k]["words_non"] += (res[k]["zero"] > 0)
                agg[k]["non"] += res[k]["zero"]
                agg[k]["inv_words"] += (res[k]["inv"] > 0)
            if any(res[k]["zero"] for k in keys):
                print("WORD", w, {f"perm{k[0]:+d}/grade{k[1]:+d}": (res[k]["esc"], res[k]["zero"], res[k]["fixed"]) for k in keys}, flush=True)
    for k in keys:
        print("TOTAL perm/grade", k, agg[k], flush=True)
    print("SEC", round(time.time() - t0), flush=True)
