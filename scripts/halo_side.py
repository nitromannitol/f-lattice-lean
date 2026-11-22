from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox
import halo_cover3 as hc

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d, T, L = frm.n, frm.d, frm.T, frm.L
    x0, x1, y0, y1 = bbox(frm)
    E = frm.inE
    out = {}
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not E(p): continue
            even = (x + y) % 2 == 0
            ins = [(x - 1, y), (x + 1, y)] if even else [(x, y - 1), (x, y + 1)]
            for u in ins:
                if E(u): continue
                side = ("W" if u[0] < x else "E") if u[1] == y else ("S" if u[1] < y else "N")
                key = (side, "even" if (u[0] + u[1]) % 2 == 0 else "odd")
                out.setdefault(key, [0, 0])
                out[key][0] += 1
    return out

if __name__ == "__main__":
    tot = {}
    with Pool(12) as pool:
        for out in pool.imap_unordered(run, list(words(4))):
            for k, v in out.items():
                tot.setdefault(k, [0, 0])
                tot[k][0] += v[0]
    print(sorted(tot.items()), flush=True)
