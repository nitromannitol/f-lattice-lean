"""Task 48: the period law of the copies (numerics, words of length <= 3).

A copy of slot k is a donor translated by its jet offset `off` and sheared by its jet slope `s`:
    copy(z) = D(z - off) + s.z + c,
where D is the donor field. The offset is a period of D (with the slope) when
    g(z) = D(z - off) + s.z - D(z)
is constant over z. We test this for each slot against the candidate fields
    Fp_w  = quarter turn of standard(swap(birth prefix of w))   (the sheet base of the even child w),
    Fp_w' = the same for the odd child w' = w + [1]              (the odd output target),
    M_w   = sheetMin of the even child w                          (the even slots 0, 1),
    F_w   = the even standard field of w.
Jets from Offsets.lean (doubleFirst / doubleLast), with K = kernel = (den, num), T = transverse = (num-den, num+den),
slope of T = (num, -den), slope of K = 0, parents of the word w itself (as in standardJets).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_copy_sheets as m  # noqa: E402

BOX = range(-5, 6)


def jets(w, par):
    """(offset, slope) for slots 0..5, from the Lean definitions with the parents of w."""
    Frm = m.Frame(list(w))
    N, D = Frm.N, Frm.D          # odd parent: num N, den D
    nq, dq = Frm.nq, Frm.dq      # even parent: num nq, den dq
    Ko, To = (D, N), (N - D, N + D)
    Ke, Te = (dq, nq), (nq - dq, nq + dq)
    so, se = (N, -D), (nq, -dq)  # slopes of T_o, T_e
    add = lambda a, b: (a[0] + b[0], a[1] + b[1])
    sc = lambda k, a: (k * a[0], k * a[1])
    Z = (0, 0)
    phase = sum(1 for x in w if x == 1) % 2
    if par == "odd":
        if phase == 0:
            off = [Z, Ke, add(add(sc(2, Ko), To), Z), add(add(sc(2, Ko), To), Ke), sc(2, Ke), Te]
            slo = [Z, Z, so, so, Z, se]
        else:
            off = [sc(2, Ko), add(sc(2, Ko), Ke), To, add(To, Ke), Z, add(sc(2, Ke), Te)]
            slo = [Z, Z, so, so, Z, se]
    else:
        if phase == 0:
            off = [Z, add(sc(2, Ko), sc(2, To)), Ke, add(Ke, To), Te, add(Te, To)]
            slo = [Z, sc(2, so), Z, so, se, add(se, so)]
        else:
            off = [sc(2, Ko), sc(2, To), Z, To, add(Te, Ke), add(add(Te, Ke), To)]
            slo = [Z, sc(2, so), Z, so, se, add(se, so)]
    return off, slo


def is_period(D, off, slope):
    vals = set()
    for x in BOX:
        for y in BOX:
            z = (x, y)
            g = D((z[0] - off[0], z[1] - off[1])) + (slope[0] * z[0] + slope[1] * z[1]) - D(z)
            vals.add(g)
            if len(vals) > 1:
                return False, None
    return True, vals.pop()


def main():
    copies = m.read_copies(m.DATA)
    groups = {}
    for cp in copies:
        groups.setdefault((cp["word"], cp["parity"]), {})[cp["slot"]] = cp
    tally = {}
    rows = []
    for (w, par), slots in sorted(groups.items(), key=lambda kv: (len(kv[0][0]), kv[0])):
        if all(d == 3 for d in w):
            continue
        off, slo = jets(w, par)
        if par == "even":
            Fp_w, A, C, M, F = m.parts(w)
            cands = {"Fp_w": Fp_w, "M_w": M, "F_w": F}
            natural = {0: "M_w", 1: "M_w", 2: "Fp_w", 3: "Fp_w", 4: "Fp_w", 5: "Fp_w"}
        else:
            Fp_c, A, C, M, F = m.parts(tuple(w) + (1,))
            cands = {"Fp_w'": Fp_c}
            natural = {k: "Fp_w'" for k in range(6)}
        for slot in range(6):
            if slot not in slots:
                continue
            nm = natural[slot]
            ok, c = is_period(cands[nm], off[slot], slo[slot])
            tally[(par, slot, nm, ok)] = tally.get((par, slot, nm, ok), 0) + 1
            if not ok:
                rows.append((''.join(map(str, w)), par, slot, nm, off[slot], slo[slot]))
    for k in sorted(tally, key=str):
        print(k, tally[k])
    print("failures (word, parity, slot, donor field, offset, slope):")
    for r in rows[:30]:
        print(" ", r)
    print("total failures:", len(rows))


if __name__ == "__main__":
    main()
