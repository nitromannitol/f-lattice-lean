"""Task 46, part 1: does each native alternate output agree with its plane target, up to a translation and a constant?

Input: scripts/data/alt_tile_dump.log (scripts/alt_tile_probe.lean: the native alternate registers after each word of
length <= 3, with their sites and heights, after llCenter).

Plane targets, from the proto recursion of the plane standard field (~/rwc-wc/fl/proto/proto2.py):
  F_u   = standard(u): the even child field of the word u (the standard field of the even child);
  sigma_u = 2 eps (D, N) with N/D the odd parent of u, eps = N d - D n, n/d the even child (Frame(u));
  G_u(x) = F_u(x + sigma_u),  H_u(x) = ceil((F_u(x) + G_u(x)) / 2)           (the alternate midpoint of the paper);
  even alternate output of w:  target H_w;
  odd alternate output of w:   target Hq((-x2, x1 - 1)) + h0(x), with Hq = H_{swap w} (the quarter turn of the swapped
                               word's H, as the standard odd output uses the quarter turn of standard(swap w)).
A tile matches when there are a translation tau and a constant c with height(x) = target(x + tau) + c on all its sites.
The ordinary alternate outputs are: odd after digits 1, 3; even after digits 1, 2. The others are the corrected ones.
"""
import re
import sys
from pathlib import Path

import ordinary_tile_check as otc

DATA = Path(__file__).parent / "data" / "alt_tile_dump.log"
DIG = {"one": 1, "two": 2, "three": 3}


def parse_log(path):
    words = []
    cur = None
    tile = None
    for line in path.read_text().splitlines():
        if line.startswith("W "):
            digits = [DIG[d] for d in re.findall(r"Digit\.(one|two|three)", line)]
            cur = {"word": tuple(digits), "odd": [], "even": []}
            words.append(cur)
            tile = None
        elif line.startswith("T "):
            tag = line.split()[1]
            tile = cur["odd" if tag == "altodd" else "even"]
        elif line.startswith("S ") and tile is not None:
            _, x, y, h = line.split()
            tile.append(((int(x), int(y)), int(h)))
    return words


def ordinary(word, parity):
    last = word[-1]
    return last in (1, 3) if parity == "odd" else last in (1, 2)


def make_targets(ns):
    standard, h0, swap, Frame = ns["standard"], ns["h0"], ns["swap"], ns["Frame"]
    cache = {}

    def H(u):
        u = tuple(u)
        if u not in cache:
            F = standard(u)[0]
            fr = Frame(list(u))
            sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
            G = lambda z, F=F, sig=sig: F((z[0] + sig[0], z[1] + sig[1]))
            cache[u] = lambda z, F=F, G=G: -((-(F(z) + G(z))) // 2)
        return cache[u]

    def target(word, parity):
        if parity == "even":
            return H(word)
        Hq = H(tuple(swap(list(word))))
        return lambda x, Hq=Hq: Hq((-x[1], x[0] - 1)) + h0(*x)

    return target


def main(argv):
    """Report, per output kind, parity and phase of the word, whether the tile fits its target at zero translation; for the
    tiles that do not, whether a translation in a small box (|tau| <= 12) fits (such fits are often accidental where the
    target is affine on the tile, so they are reported separately)."""
    ns = otc.load_proto()
    target_of = make_targets(ns)
    words = parse_log(DATA)
    print("words %d" % len(words))
    tally = {}
    details = []
    for entry in words:
        w = entry["word"]
        phase = sum(1 for d in w if d == 1) % 2
        for parity in ("odd", "even"):
            sites = entry[parity]
            if not sites:
                continue
            kind = "ordinary" if ordinary(w, parity) else "corrected"
            target = target_of(w, parity)
            if otc.fit(sites, target, [(0, 0)]) is not None:
                status = "fits at tau=0"
            else:
                box = [(a, b) for a in range(-12, 13) for b in range(-12, 13)]
                r = otc.fit(sites, target, box)
                status = "fits with shift in box" if r else "NO FIT"
                if r:
                    details.append((w, parity, kind, "shift", r))
                else:
                    details.append((w, parity, kind, "NO FIT", None))
            key = (kind, parity, "phase %d" % phase, status)
            tally[key] = tally.get(key, 0) + 1
    print("tally (kind, parity, phase, status):")
    for k in sorted(tally):
        print("  ", k, tally[k])
    print("tiles not fitting at tau=0 (word, parity, kind, status, fit):")
    for d in details:
        print("  ", d)


if __name__ == "__main__":
    main(sys.argv[1:])
