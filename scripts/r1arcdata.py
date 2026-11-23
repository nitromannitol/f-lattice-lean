"""Task 55 (S2 arc data): the register tiles' arcs satisfy the hypotheses of rows_of_boundary.

For a register tile P (odd or even) of state(w), with boundary arcs w1 (first) and w2 (second) traced from (0,0):
  (a) every letter of w1 is one or i; (b) every letter of w2 is i or -1;
  (c) n1 < n2, where n1 = #i(w1), n2 = #i(w2);  (d) 0 < s1 + s2, the x-sums of w1 and w2;
  (e) not (last w1 = one and head w2 = -1)   (Ra);   (f) not (head w1 = i and last w2 = i)   (Rb);
  (g) last w2 = i.
Checked for words up to length L with the invariants (odd register: a letter 1 or 2 read; even: a letter 1 or 3 read).
Usage: python3 r1arcdata.py L"""
import sys
from collections import Counter
from standard_tiles import words, state, cellTile
from seamwords_cmp import tile_arcs
from r1structure import run

def letters(arc):
    return [t for t in arc.split(",") if t]

def arc_data(w1, w2):
    ok = {}
    ok["a"] = all(x in ("1", "i") for x in w1)
    ok["b"] = all(x in ("i", "-1") for x in w2)
    n1 = sum(1 for x in w1 if x == "i"); n2 = sum(1 for x in w2 if x == "i")
    ok["c"] = n1 < n2
    s1 = sum(1 if x == "1" else (-1 if x == "-1" else 0) for x in w1)
    s2 = sum(1 if x == "1" else (-1 if x == "-1" else 0) for x in w2)
    ok["d"] = s1 + s2 > 0
    ok["e"] = not (w1 and w2 and w1[-1] == "1" and w2[0] == "-1")
    ok["f"] = not (w1 and w2 and w1[0] == "i" and w2[-1] == "i")
    ok["g"] = bool(w2) and w2[-1] == "i"
    return ok

def main(L):
    tally = Counter(); bad = []
    for w in words(L):
        if not w: continue
        (rO, rE), _ = run(w)
        par, tO, tE = state(w)
        for name, T, inv in (("odd", tO, any(x in (1, 2) for x in w)), ("even", tE, any(x in (1, 3) for x in w))):
            if not inv: continue
            arcs = tile_arcs(cellTile(T))
            if arcs is None:
                tally[(name, "no arcs")] += 1; continue
            w1, w2 = letters(arcs[0]), letters(arcs[1])
            ok = arc_data(w1, w2)
            tally[(name, "checked")] += 1
            for k, v in ok.items():
                if not v:
                    tally[(name, "fails " + k)] += 1
                    if len(bad) < 3: bad.append((name, ''.join(map(str, w)), k, arcs[0], arcs[1]))
            if all(ok.values()): tally[(name, "all hypotheses")] += 1
    for k in sorted(tally, key=str): print(k, tally[k])
    print("examples of failures:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
