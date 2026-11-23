"""Task 59 step 2, the exit lemma's named hypotheses (PROVISIONAL, from W1_CONSTRUCTOR sec. 1), words <= 4:
  hRect:     for w in E with w in the open parity rectangle, both inputs of w lie in E.
  hBoundary: for w in E outside the open rectangle, w is on a boundary spectrum mod T:
             t in H-spectrum +- kT or s in V-spectrum +- kT (k = 0, +-1).
Rectangle (parity chi, (a_e,b_e)=(2,L-2), (a_o,b_o)=(n,d); (c_e,h_e)=(0,2n), (c_o,h_o)=(2-d+n,L-2)):
  even: b_e - T < t < a_e and h_e < s < T + c_e;   odd: b_o - T < t < a_o and h_o < s < T + c_o.
"""
from multiprocessing import Pool
from collections import defaultdict
import open_inputs_check as oc
from exact_quotient import words


def run(w):
    w = list(w)
    fr = oc.frame(w)
    N, D, n, d, T = fr["N"], fr["D"], fr["n"], fr["d"], fr["T"]
    L = n + d
    tg = lambda z: n * z[0] - d * z[1]
    sg = lambda z: L * z[0] + (d - n) * z[1]
    x0, x1, y0, y1 = oc.window(fr)
    inE = lambda z: oc.in_polygon(z, fr)
    reps = [(x, y) for x in range(x0, x1 + 1) for y in range(y0, y1 + 1) if inE((x, y))]
    Hspec = set(range(2, L - 1, 2)) | set(range(n, d + 1, 2))
    Vspec = set(range(0, 2 * n + 1, 2)) | set(range(2 - d + n, L - 1, 2))
    def rect(z):
        t, s = tg(z), sg(z)
        if oc.even_site(z):
            return (L - 2 - T < t < 2) and (2 * n < s < T)
        return (d - T < t < n) and (L - 2 < s < T + 2 - d + n)
    out = defaultdict(int)
    for z in reps:
        if rect(z):
            out[("rect point", True)] += 1
            for i in (oc.incoming_neg(z), oc.incoming_pos(z)):
                out[("rect input in E", inE(i))] += 1
        else:
            out[("E outside rect", True)] += 1
            t, s = tg(z), sg(z)
            onb = any(((t + k * T) in Hspec) for k in (-1, 0, 1)) or any(((s + k * T) in Vspec) for k in (-1, 0, 1))
            out[("outside rect is on boundary spectrum mod T", onb)] += 1
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
