"""Task 42: does the native ordinary standard output tile equal the plane standard field, up to a constant?

Input: scripts/data/ordinary_tile_dump.log, written by scripts/ordinary_tile_probe.lean (the Lean native constructor,
`evaluateNative` after each word of length <= 3). Each word gives its output tiles `odd` and `even` (sites, heights).
Only the parities the constructor uses as ordinary are compared: digit one both, digit two odd, digit three even.

Plane targets, from ~/rwc-wc/fl/proto/proto2.py (the recursion of the plane standard field):
  even output of word w: the even child of w, target = standard(w)(x);
  odd output of word w: the odd child of w, which is the odd parent of w + [one]; its field is
      Fp(x) = standard(swap w)((-x2, x1 - 1)) + h0(x)   (the quarter turn of the conjugate standard field).
For each tile we look for a translation tau and a constant c with  tile(x) = target(x + tau) + c  on all sites x.
tau = 0 is tested first; otherwise tau ranges over a box.
"""
import re
import sys
from pathlib import Path

PROTO = Path.home() / "rwc-wc" / "fl" / "proto" / "proto2.py"
DATA = Path(__file__).parent / "data" / "ordinary_tile_dump.log"
DIG = {"one": 1, "two": 2, "three": 3}


def load_proto():
    src = PROTO.read_text()
    cut = src.index("for L_ in range(1,4):")
    ns = {}
    exec(compile(src[:cut], "proto2_defs", "exec"), ns)
    return ns


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
            tile = cur[tag]
        elif line.startswith("S ") and tile is not None:
            _, x, y, h = line.split()
            tile.append(((int(x), int(y)), int(h)))
    return words


def ordinary(word, parity):
    last = word[-1]
    return last == 1 or (last == 2 and parity == "odd") or (last == 3 and parity == "even")


def fit(sites, target, box):
    """Return (tau, c) with h(x) = target(x + tau) + c on all sites, searching tau in box; None if no fit."""
    xs = [x for x, _ in sites]
    hs = dict(sites)
    for tau in box:
        vals = {x: hs[x] - target((x[0] + tau[0], x[1] + tau[1])) for x in xs}
        c = next(iter(vals.values()))
        if all(v == c for v in vals.values()):
            return tau, c
    return None


def main():
    ns = load_proto()
    standard, h0, swap = ns["standard"], ns["h0"], ns["swap"]
    words = parse_log(DATA)
    print(f"words {len(words)}")
    results = []
    for entry in words:
        w = entry["word"]
        for parity in ("odd", "even"):
            if not ordinary(w, parity):
                continue
            sites = entry[parity]
            if parity == "even":
                F = standard(tuple(w))[0]
                target = F
            else:
                Fq = standard(tuple(swap(list(w))))[0]
                target = lambda x, Fq=Fq: Fq((-x[1], x[0] - 1)) + h0(*x)
            xs = [x for x, _ in sites]
            if not xs:
                results.append((w, parity, "empty", None))
                continue
            span = max(max(abs(x), abs(y)) for x, y in xs)
            r0 = fit(sites, target, [(0, 0)])
            if r0 is not None:
                results.append((w, parity, "fits at tau=0", r0))
                continue
            B = min(span + 8, 40)
            box = [(a, b) for a in range(-B, B + 1) for b in range(-B, B + 1)]
            r = fit(sites, target, box)
            results.append((w, parity, "fits with shift" if r else "NO FIT", r))
    tally = {}
    for w, parity, status, r in results:
        tally[status] = tally.get(status, 0) + 1
    print("tally", tally)
    for w, parity, status, r in results:
        if status != "fits at tau=0":
            print(w, parity, status, r)


if __name__ == "__main__":
    main()
