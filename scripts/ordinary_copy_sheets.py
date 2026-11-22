"""Task 44: which plane object does each of the six placed copies of an ordinary standard reproduce on its sites?

Plane objects (from ~/rwc-wc/fl/proto/proto2.py, the recursion of the plane standard field), for a child word w:
  F_w   = standard(w): the even child field of w (periodized sewn field).
  Fp_w  = quarter turn of standard(swap(birth prefix of w)): the odd parent field used by w's sheets.
  A_w, C_w, M_w = the two sheets A, C and their minimum M, built from Fp_w exactly as in proto2's standard(w).
For the odd output at word u, the target is Fp_{u+[1]} (= quarter turn of standard(swap u)), and its sheets are the sheets
of the odd child u+[1].

Input: scripts/data/ordinary_copy_dump.log (from scripts/ordinary_copy_dump_probe.lean): `COPY <word> <parity> <slot>` then
`S <x> <y> <h>` for each site of the copy (raw chart = plane chart, since the origin is zero).
Test: copy(s) = cand(s + tau) + c for all sites s, with a constant c, for a translation tau in a box.
Candidates in order: A, C, M (sheets of the child), T (the target), Fp (the other parity's field), each at tau in the box.
"""
import re
import sys
from pathlib import Path

PROTO = Path.home() / "rwc-wc" / "fl" / "proto" / "proto2.py"
DATA = Path(__file__).parent / "data" / "ordinary_copy_dump.log"
DIG = {"one": 1, "two": 2, "three": 3}
BOX = 6


def load_proto():
    src = PROTO.read_text()
    cut = src.index("for L_ in range(1,4):")
    ns = {}
    exec(compile(src[:cut], "proto2_defs", "exec"), ns)
    return ns


NS = load_proto()
standard, h0, swap, Frame = NS["standard"], NS["h0"], NS["swap"], NS["Frame"]
_parts_cache = {}


def parts(w):
    """Return (Fp, A, C, M, F) for a proper word w (tuple of 1,2,3), as plane functions on sites."""
    w = tuple(w)
    if w in _parts_cache:
        return _parts_cache[w]
    k = max(i for i, x in enumerate(w) if x in (1, 2))
    wp = list(w[:k])
    Fq = standard(tuple(swap(wp)))[0]
    Fp = lambda x, Fq=Fq: Fq((-x[1], x[0] - 1)) + h0(*x)
    fr = Frame(list(w))
    N, D, nq, dq = fr.N, fr.D, fr.nq, fr.dq
    eps = fr.eps
    W = (1 + eps) // 2
    Uq = (dq, nq)
    Vq = (nq - dq, dq + nq)
    lv = ((1 - W) * Uq[0], (1 - W) * Uq[1])
    e = (Vq[0] + eps * Uq[0], Vq[1] + eps * Uq[1])
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    A = lambda z: Fp((z[0] - lv[0], z[1] - lv[1]))
    C = lambda z: (Fp((z[0] - lv[0] - e[0], z[1] - lv[1] - e[1])) + nq * (z[0] - lv[0]) - dq * (z[1] - lv[1]) + ce)
    M = lambda z: min(A(z), C(z))
    F = standard(w)[0]
    _parts_cache[w] = (Fp, A, C, M, F)
    return _parts_cache[w]


def read_copies(path):
    copies = []
    cur = None
    for line in path.read_text().splitlines():
        if line.startswith("COPY "):
            m = re.match(r"COPY \[(.*)\] (\S+) (\d)$", line)
            w = tuple(DIG[d] for d in re.findall(r"Digit\.(one|two|three)", line))
            par = "odd" if "Parity.odd" in line else "even"
            slot = int(line.split()[-1])
            cur = {"word": w, "parity": par, "slot": slot, "sites": []}
            copies.append(cur)
        elif line.startswith("S ") and cur is not None:
            _, x, y, h = line.split()
            cur["sites"].append(((int(x), int(y)), int(h)))
    return copies


def targets(word, parity):
    """The plane target of the output at `word` and its sheet child."""
    if parity == "even":
        Fp, A, C, M, F = parts(word)
        return {"A": A, "C": C, "M": M, "T": F, "Fp": Fp}
    child = tuple(word) + (1,)
    Fp, A, C, M, F = parts(child)
    return {"A": A, "C": C, "M": M, "T": Fp, "Fp": None}


def fits(sites, cand, tau):
    vals = []
    for (x, h) in sites:
        vals.append(h - cand((x[0] + tau[0], x[1] + tau[1])))
    return vals[0] if all(v == vals[0] for v in vals) else None


def classify(copy):
    sites = copy["sites"]
    if not sites:
        return ("empty", None, None)
    word, parity = copy["word"], copy["parity"]
    if all(d == 3 for d in word):
        return ("skip-threes", None, None)
    cands = targets(word, parity)
    order = ["A", "C", "M", "T", "Fp"]
    taus = sorted(((a, b) for a in range(-BOX, BOX + 1) for b in range(-BOX, BOX + 1)),
                  key=lambda t: abs(t[0]) + abs(t[1]))
    for name in order:
        cand = cands.get(name)
        if cand is None:
            continue
        for tau in taus:
            c = fits(sites, cand, tau)
            if c is not None:
                return (name, tau, c)
    return ("NONE", None, None)


def main():
    copies = read_copies(DATA)
    print(f"copies {len(copies)}")
    table = {}
    for cp in copies:
        label = classify(cp)
        table[(cp["word"], cp["parity"], cp["slot"])] = label
    for key in sorted(table, key=lambda k: (len(k[0]), k[0], k[1], k[2])):
        w, par, slot = key
        lab, tau, c = table[key]
        print(f"{''.join(map(str, w)):>3} {par:4} slot {slot}: {lab} tau={tau} c={c}")


if __name__ == "__main__":
    main()
