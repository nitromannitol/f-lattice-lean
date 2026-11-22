"""Seven-copy table for the ordinary even alternate (task 46).

Reads scripts/data/alt_copy_dump.log (written by alt_copy_probe.lean: for each word w of length at most three ending in 1 or
2, the first copy and the six copies of ordinaryAlternateSchedule at parity even, with their sites and heights).

Default output: for each word and each copy, whether the copy agrees at zero translation with the alternate midpoint
H(w) = ceil((F + F(. + 2 eps (D, N)))/2) of the word itself (F = standard even field of w, frame of w), up to one
additive constant, and the number of sites of the copy.

With `--scan`: for each copy, the candidate plane objects (E, O, H, Q over all words of length at most three) it fits at
zero translation. Small tiles fit many candidates, so the scan is only indicative.
"""
import itertools
import sys
from collections import defaultdict

import ordinary_tile_check as otc

DUMP = "/Users/ahmedbou-rabee/lean-work/flattice-wt/w2/scripts/data/alt_copy_dump.log"
DIGIT = {"one": 1, "two": 2, "three": 3}
TAGS = ["first", "seventh", "slot1", "slot2", "slot3", "slot4", "slot5"]


def parse_dump(path):
    words = {}
    cur = None
    tag = None
    with open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if line.startswith("W "):
                body = line[line.index("[") + 1: line.rindex("]")]
                cur = tuple(DIGIT[t.strip().rsplit(".", 1)[-1]] for t in body.split(","))
                words[cur] = {}
            elif line.startswith("T "):
                _, tag, _count = line.split()
                words[cur][tag] = []
            elif line.startswith("S "):
                _, x, y, h = line.split()
                words[cur][tag].append(((int(x), int(y)), int(h)))
    return words


def fits_zero(sites, target):
    """True when height(x) - target(x) is one constant on the sites, at zero translation (early exit)."""
    c = None
    for x, h in sites:
        d = h - target(x)
        if c is None:
            c = d
        elif d != c:
            return False
    return c is not None


def make_fields(ns):
    standard, h0, swap, Frame = ns["standard"], ns["h0"], ns["swap"], ns["Frame"]

    def E(u):
        return standard(tuple(u))[0]

    def H(u):
        Fu = E(u)
        fr = Frame(list(u))
        sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
        return lambda z: -((-(Fu(z) + Fu((z[0] + sig[0], z[1] + sig[1])))) // 2)

    def O(u):
        Fs = E(swap(list(u)))
        return lambda x: Fs((-x[1], x[0] - 1)) + h0(*x)

    def Q(u):
        Hs = H(swap(list(u)))
        return lambda x: Hs((-x[1], x[0] - 1)) + h0(*x)

    return E, H, O, Q


def main(argv):
    ns = otc.load_proto()
    ends = {w: d for w, d in parse_dump(DUMP).items() if w and w[-1] in (1, 2)}
    E, H, O, Q = make_fields(ns)
    print("word      " + "  ".join(f"{t:>9}" for t in TAGS))
    total = 0
    fitted = 0
    misses = []
    for w in sorted(ends, key=lambda t: (len(t), t)):
        Hw = H(list(w))
        row = []
        for t in TAGS:
            sites = ends[w][t]
            ok = fits_zero(sites, Hw)
            row.append("%s(%d)" % ("H" if ok else "-", len(sites)))
            total += 1
            fitted += ok
            if not ok:
                misses.append((w, t))
        print("%-9s" % str(w) + "  ".join(f"{r:>9}" for r in row))
    print("copies agreeing with H(w) at zero translation: %d of %d" % (fitted, total))
    print("misses (word, copy):", misses)

    if "--scan" in argv:
        universe = [()]
        for n in (1, 2, 3):
            universe += list(itertools.product((1, 2, 3), repeat=n))
        kinds = {"E": E, "O": O, "H": H, "Q": Q}
        for w in sorted(ends, key=lambda t: (len(t), t)):
            for t in TAGS:
                sites = ends[w][t]
                found = []
                for u in universe:
                    for kname, kf in kinds.items():
                        try:
                            tgt = kf(list(u))
                        except Exception:
                            continue
                        if fits_zero(sites, tgt):
                            found.append(f"{kname}{list(u)}")
                print(w, t, found)


if __name__ == "__main__":
    main(sys.argv[1:])
