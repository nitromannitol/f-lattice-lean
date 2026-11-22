"""Task 48: for each odd copy, the translation v with copy(z) = Fp_w'(z + v) + c on all its sites, and whether L v lies in
the conjugate lattice Lambda_s = span(mu_s K_s, T_s) (L(v) = (-v2, v1), the linear part of the quarter turn).
Searched over |v_1|, |v_2| <= 6. Also the constant c and the smallest fitting v per slot (first tile of each slot).
"""
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402

RANGE = range(-6, 7)


def lattice(fr):
    n, d = fr.n, fr.d
    mu = 1 if (n + d) % 2 == 0 else 2
    return (mu * d, mu * n), (n - d, n + d)


def in_lattice(u, K, T):
    # solve u = i K + j T over the integers
    det = K[0] * T[1] - K[1] * T[0]
    if det == 0:
        return False
    i_num = u[0] * T[1] - u[1] * T[0]
    j_num = K[0] * u[1] - K[1] * u[0]
    return i_num % det == 0 and j_num % det == 0


def fits(sites, Fp, v):
    vals = set()
    for (x, h) in sites:
        vals.add(h - Fp((x[0] + v[0], x[1] + v[1])))
        if len(vals) > 1:
            return None
    return vals.pop()


def main():
    copies = m.read_copies(m.DATA)
    st = Counter()
    examples = {}
    for cp in copies:
        w, par, slot = cp["word"], cp["parity"], cp["slot"]
        if par != "odd" or not cp["sites"] or all(d == 3 for d in w):
            continue
        wp = tuple(w) + (1,)
        Fp = m.parts(wp)[0]
        sw = tuple(m.swap(list(w)))
        K, T = lattice(m.Frame(list(sw)))
        found = []
        for a in RANGE:
            for b in RANGE:
                c = fits(cp["sites"], Fp, (a, b))
                if c is not None:
                    found.append(((a, b), c))
        in_l = [(v, c) for v, c in found if in_lattice((-v[1], v[0]), K, T)]
        st[(slot, "fitting v", len(found) > 0, "Lv in Lambda_s for some fitting v", len(in_l) > 0)] += 1
        if slot not in examples and found:
            examples[slot] = (''.join(map(str, w)), found[0], in_l[0] if in_l else None)
    for k in sorted(st, key=str):
        print(k, st[k])
    for slot in sorted(examples):
        print("slot", slot, "example (word, first fitting (v, c), first with Lv in lattice):", examples[slot])


if __name__ == "__main__":
    main()
