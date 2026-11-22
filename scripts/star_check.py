"""Task 32 (S1, S2): D = F - F(.+sigma), sigma = shortShift = 2 eps (D_odd, N_odd).
Over the E-representatives of all classes (E = permit_local.Frame.inE, a fundamental domain; arcs_check.e_rep):
  R_E   : D in {0,1,2} at every site of E                      (STRONG section 2: D+(E) in {0,1,2})
  R_in  : D in {0,1,2} at every input of an E site             (the 'E and its inputs' range)
  UJ    : |D(u) - D(y)| <= 1 on every edge u -> y with y in E  (STRONG section 3/4: unit jumps; = HasUnitSlip)
  X02   : no edge with {D(y), D(u)} = {0, 2} with y in E        (hJ of star_of_closedPolygon)
  NES   : NoEvenSlipSaddle at every E site (even gap: D(y) even): not (neg,pos) = (-1,+1) or (+1,-1), where
          neg = D(incomingNeg y) - D(y), pos = D(incomingPos y) - D(y)."""
from multiprocessing import Pool
import permit_local as pl
from arcs_check import e_rep
from exact_quotient import words

def run(w):
    w = list(w)
    F, _ = pl.standard(tuple(w))
    fr = pl.Frame(w)
    N, D_ = pl.parents(w)[0]
    sig = (2 * fr.eps * D_, 2 * fr.eps * N)
    Dfun = lambda z: F(z) - F((z[0] + sig[0], z[1] + sig[1]))
    import restricted_escape as re_
    systems, _ = re_.systems_for(w)
    lap, perm, tg, K, V = systems["S3"]
    det, S0 = re_.cover_sites(K, V)
    counts = dict(classes=0, RE=0, Rin=0, UJ=0, X02=0, NES=0)
    for z in S0:
        y = e_rep(fr, z)
        counts["classes"] += 1
        dy = Dfun(y)
        ins = pl.neighbours(y)
        dins = [Dfun(u) for u in ins]
        if dy in (0, 1, 2):
            counts["RE"] += 1
        if all(d in (0, 1, 2) for d in dins):
            counts["Rin"] += 1
        if all(abs(d - dy) <= 1 for d in dins):
            counts["UJ"] += 1
        if not any((dy == 0 and d == 2) or (dy == 2 and d == 0) for d in dins):
            counts["X02"] += 1
        if dy % 2 == 0:
            neg, pos = dins[0] - dy, dins[1] - dy
            if not ((neg == -1 and pos == 1) or (neg == 1 and pos == -1)):
                counts["NES"] += 1
        else:
            counts["NES"] += 1
    return tuple(w), counts

if __name__ == "__main__":
    ws = list(words(4))
    tot = dict(classes=0, RE=0, Rin=0, UJ=0, X02=0, NES=0)
    bad = []
    with Pool(12) as pool:
        for w, c in pool.imap_unordered(run, ws):
            for k in tot:
                tot[k] += c[k]
            if any(c[k] != c["classes"] for k in ("RE", "Rin", "UJ", "X02", "NES")):
                bad.append((w, c))
    print("TOTAL", tot, flush=True)
    print("WORDS_WITH_FAILURES", len(bad), flush=True)
    for w, c in sorted(bad, key=lambda x: (len(x[0]), x[0]))[:6]:
        print("WORD", w, c, flush=True)
