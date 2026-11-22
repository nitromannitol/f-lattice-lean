"""Task 33 (B) numerics: the inputs of StarRangeArgument.lean over all E classes (E representatives), all 116 words.
  triple: for each E site y, the values of D on its full star {y, neg y, pos y} lie in [c, c+2] for some even c;
  base:   every even c with the star values in [c, c+2] equals 0;
  binary difference: laplacian(D) at y lies in {-1, 0, 1} (it equals lap F(y) - lap F(y + sigma))."""
from multiprocessing import Pool
import permit_local as pl
import restricted_escape as re_
from arcs_check import e_rep
from exact_quotient import words

def run(w):
    w = list(w)
    systems, fr = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    F, _ = pl.standard(tuple(w))
    N, Dd = pl.parents(w)[0]
    sig = (2 * fr.eps * Dd, 2 * fr.eps * N)
    D = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    det, S0 = re_.cover_sites(K, V)
    c_triple = c_base = c_lap = 0
    windows_ok = 0
    for r in S0:
        y = e_rep(fr, r)
        star = [D(y), D(pl.neighbours(y)[0]), D(pl.neighbours(y)[1])]
        lo, hi = min(star), max(star)
        evens = [c for c in range(lo - 2, hi + 1) if c % 2 == 0 and lo >= c and hi <= c + 2]
        if evens:
            c_triple += 1
            if all(c == 0 for c in evens):
                c_base += 1
        n0, n1 = pl.neighbours(y)
        l = D(n0) + D(n1) - 2 * D(y)
        if -1 <= l <= 1:
            c_lap += 1
    return tuple(w), len(S0), c_triple, c_base, c_lap

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, triple=0, base=0, lap=0)
    bad = []
    with Pool(12) as pool:
        for w, n, t, b, l in pool.imap_unordered(run, ws):
            tot["classes"] += n; tot["triple"] += t; tot["base"] += b; tot["lap"] += l
            if not (t == n and b == n and l == n):
                bad.append((w, n, t, b, l))
    print("TOTAL", tot, flush=True)
    print("WORDS_WITH_FAILURES", len(bad), flush=True)
    for x in sorted(bad, key=lambda x: (len(x[0]), x[0]))[:6]:
        print("WORD", x, flush=True)
