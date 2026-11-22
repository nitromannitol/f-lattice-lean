"""Minima of pairs of sheets for the copies that are not single sheets (task 46).

For a copy whose heights are not one sheet, test whether copy = min(X, Y) + const on its sites, for the pairs X, Y among
A, C, A(. + sigma), C(. + sigma) (and F = min(A, C) for the first copy), and report the pairs that fit with one constant.
"""
import itertools
from sheet_table import copy, TAGS
from sheets import sheets
from slot3_check import classify

if __name__ == "__main__":
    for w in sorted([w for w in copy if w and w[-1] in (1, 2) and not all(d == 2 for d in w)], key=lambda t: (len(t), t)):
        cls, sig = classify(w)
        A, C, info = sheets(w)
        sh = lambda s, sg: (s[0] + sg[0], s[1] + sg[1])
        cands = {
            "A": A,
            "C": C,
            "A+s": lambda s: A(sh(s, sig)),
            "C+s": lambda s: C(sh(s, sig)),
        }
        out = []
        for t in TAGS:
            sites = copy[w][t]
            hits = []
            for (n1, X), (n2, Y) in itertools.combinations(cands.items(), 2):
                ks = set(hs - min(X(s), Y(s)) for (s, hs) in sites)
                if len(ks) == 1:
                    hits.append(f"min({n1},{n2})")
            if t == "first":
                ks = set(hs - min(A(s), C(s)) for (s, hs) in sites)
                if len(ks) == 1:
                    hits.append("min(A,C)=F")
            out.append(f"{t}:{'/'.join(hits) if hits else '-'}")
        print(w, cls, " ".join(out), flush=True)
