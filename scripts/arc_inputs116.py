"""Task 34 (3): the inputs of the base argument checked on E's lattice boundary, all 116 words.
Boundary sites: E points with an outside 4-neighbour; outward pattern in {N,S,E,W} combinations.
  bottomZero: pure-S sites (outward S, not W, not E): D+ = 0      (B2 audit section 1: bottom H vanishes)
  topTwo:     pure-N sites (outward N, not W, not E): D+ = 2      (B2 audit: top H is 2 by its V character)
  leftRange:  sites with outward W or E: D+ in {0,1,2}          (B2 audit: ancestral V cut, right V by U character)
  patterns:   no boundary site has outward {N,S} or {E,W}       (E is a parallelogram with unit connectors)
  rightShift: the E-outward boundary sites are exactly the W-outward boundary sites shifted by U (D+ equal)
  range:      D+ in {0,1,2} on all of E (conclusion of the comparison, checked numerically)."""
from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words

def bbox(frm):
    T, L, n, d = frm.T, frm.L, frm.n, frm.d
    xs, ys = [], []
    for (t, s) in [(2 - T, 0), (2 - T, T + 2 * n), (L - 2, 0), (L - 2, T + 2 * n),
                   (n - T, 2 - d + n), (n - T, T + L - 2), (d, 2 - d + n), (d, T + L - 2)]:
        # invert [[n,-d],[L,d-n]] (x,y) = (t,s); det = T
        x = ((d - n) * t + d * s) / T
        y = (n * s - L * t) / T
        xs.append(x); ys.append(y)
    return int(min(xs)) - 3, int(max(xs)) + 3, int(min(ys)) - 3, int(max(ys)) + 3

def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    frm = pl.Frame(w)
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    Dp = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    x0, x1, y0, y1 = bbox(frm)
    c = dict(bottom=0, bottom_bad=0, top=0, top_bad=0, left=0, left_bad=0, pattern_bad=0, nbound=0,
             out_E_count=0, out_W_count=0, shift_bad=0, range_bad=0, E_points=0)
    outs = {}
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            c["E_points"] += 1
            val = Dp(p)
            if not (0 <= val <= 2):
                c["range_bad"] += 1
            out = frozenset(nm for nm, d in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                            if not frm.inE((x + d[0], y + d[1])))
            if not out:
                continue
            c["nbound"] += 1
            outs[p] = out
            if ("N" in out and "S" in out) or ("E" in out and "W" in out):
                c["pattern_bad"] += 1
            if out == {"S"}:
                c["bottom"] += 1
                if val != 0:
                    c["bottom_bad"] += 1
            if out == {"N"}:
                c["top"] += 1
                if val != 2:
                    c["top_bad"] += 1
            if "W" in out or "E" in out:
                c["left"] += 1
                if not (0 <= val <= 2):
                    c["left_bad"] += 1
            if "E" in out:
                c["out_E_count"] += 1
    # rightShift: an E-outward boundary point p has p - U in the W-outward set with equal D+ (U = kernel period)
    U = (frm.d, frm.n)
    for p, out in outs.items():
        if "E" in out:
            q = (p[0] - U[0], p[1] - U[1])
            if q not in outs or "W" not in outs[q] or Dp(q) != Dp(p):
                c["shift_bad"] += 1
        if "W" in out:
            c["out_W_count"] += 1
    return tuple(w), c

if __name__ == "__main__":
    ws = list(words(4))
    tot = {}
    with Pool(12) as pool:
        for w, c in pool.imap_unordered(run, ws):
            for k, v in c.items():
                tot[k] = tot.get(k, 0) + v
    print("TOTAL", tot, flush=True)
