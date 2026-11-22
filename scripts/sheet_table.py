"""Which sheet of the standard even field of a word each copy of its ordinary even alternate reproduces (task 46).

For each word w (ending in 1 or 2, length at most three) and each copy tag, test whether the copy equals one of the sheets
A, C of w, or the same sheets shifted by sigma (A(s + sigma), C(s + sigma)), up to one constant on its sites. The alternate
output H(w) is min(F, F(. + sigma) + 1) with F = min(A, C) on the window, so a copy is one of these four sheets (plus 1) on its
sites, or a mix of them.
"""
import alt_copy_check as acc
from sheets import sheets
from slot3_check import classify

copy = acc.parse_dump(acc.DUMP)
TAGS = ["first", "seventh", "slot1", "slot2", "slot3", "slot4", "slot5"]
if __name__ == "__main__":
    for w in sorted([w for w in copy if w and w[-1] in (1, 2) and not all(d == 2 for d in w)], key=lambda t: (len(t), t)):
        cls, sig = classify(w)
        A, C, info = sheets(w)
        cands = {
            "A": A,
            "C": C,
            "A(+sig)": lambda s, A=A, sig=sig: A((s[0] + sig[0], s[1] + sig[1])),
            "C(+sig)": lambda s, C=C, sig=sig: C((s[0] + sig[0], s[1] + sig[1])),
        }
        row = []
        for t in TAGS:
            sites = copy[w][t]
            fits = []
            for name, X in cands.items():
                ks = set(hs - X(s) for (s, hs) in sites)
                if len(ks) == 1:
                    fits.append(name)
            row.append(f"{t}:{'/'.join(fits) if fits else '-'}")
        print(w, cls, " ".join(row), flush=True)
