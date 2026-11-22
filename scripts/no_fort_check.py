"""Exact no-fort check (RestrictedNoFort) for the two systems whose grades are computed correctly by exact_quotient.py:

  S3  : field F = standardField word, permits slipPermits F (F(. + sigma)), grade cutGrade F 1 1 1 (eta = +1),
        deck = the child's modified deck (as in restricted_escape.systems_for).
  I3C : field Fp, permits Xi(. + off) <= Xi(. + off), grade tGrade (child t), deck = odd parent's modified deck.

For each word, the exact quotient escape test of exact_quotient.quotient_T gives the sites that do not escape
at their own level, n_nonesc. A non-escaping site p with g(p) = L gives a restricted fort in {grade >= L}
(its non-escaping sites with grade >= L), so n_nonesc = 0 for every word is the numerical content of
RestrictedNoFort on the quotient. I3A (grade cutGrade on G transported by the quarter turn, eta = eps) is
checked by i3a_conj.py, which uses the transported grade; exact_quotient.py uses Fp for I3A and is not used.
"""
import sys
from multiprocessing import Pool

import exact_quotient as eq
import permit_local as pl
import restricted_escape as re_


def run(w):
    w = list(w)
    systems, _ = re_.systems_for(w)
    F, _ = pl.standard(tuple(w))
    out = {}
    specs = {
        "S3": (systems["S3"][0], systems["S3"][1], eq.cut_on(F, w, 1, 1, 1), systems["S3"][3], systems["S3"][4]),
        "I3C": (systems["I3C"][0], systems["I3C"][1], systems["I3C"][2], systems["I3C"][3], systems["I3C"][4]),
    }
    for name, (lap, perm, grade, K, V) in specs.items():
        n, S0, g, lapv, edges, _ = eq.build(K, V, lap, perm, grade)
        T, capped = eq.quotient_T(n, g, lapv, edges, exact=True)
        nonesc = [S0[p] for p in range(n) if not (T[p] <= g[p])]
        out[name] = dict(n=n, nonesc=len(nonesc), capped=capped, sample=nonesc[:3])
    return tuple(w), out


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    ws = list(pl.proper_words(maxlen))
    tot = {k: [0, 0, 0] for k in ("S3", "I3C")}
    with Pool(12) as pool:
        for w, res in pool.imap_unordered(run, ws):
            for k in tot:
                r = res[k]
                tot[k][0] += (r["nonesc"] > 0)
                tot[k][1] += r["nonesc"]
                tot[k][2] += r["capped"]
                if r["nonesc"] or r["capped"]:
                    print("BAD", k, "".join(map(str, w)), r, flush=True)
    print("proper words:", len(ws))
    for k in tot:
        print("TOTAL", k, "words_with_nonescape", tot[k][0], "nonescape_sites", tot[k][1], "capped", tot[k][2])
