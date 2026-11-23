"""Task 59 step 2 (Q3 paragraph 2): the physical inputs of black centers lie in the closed polygon E (words <= 4).

For each representative c in E: lap(F, c) = -1 means black. Checks whether incomingNeg(c) and incomingPos(c) lie in E.
Also reports, for white centers, how many inputs leave E (the boundary whites whose inputs are outside E).
"""
from multiprocessing import Pool
from collections import defaultdict
import permit_local as pl
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    fr = oc.frame(w)
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    out = defaultdict(int)
    for c in reps:
        lv = pl.lap(F, c)
        ins = [oc.incoming_neg(c), oc.incoming_pos(c)]
        outside = sum(1 for i in ins if not inE(i))
        if lv == -1:
            out[("black centers", "inputs outside E = %d" % outside)] += 1
        else:
            out[("white centers", "inputs outside E = %d" % outside)] += 1
    return out


if __name__ == "__main__":
    ws = [list(x) for x in words(4)]
    tot = defaultdict(int)
    with Pool(12) as pool:
        for out in pool.imap_unordered(run, ws):
            for k, v in out.items():
                tot[k] += v
    for k in sorted(tot, key=str):
        print(k, tot[k], flush=True)
