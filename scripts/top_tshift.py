from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d, T = frm.n, frm.d, frm.T
    V = (n - d, n + d)
    x0, x1, y0, y1 = bbox(frm)
    tops, ok_strip, ok_strip_sig, ts_top = 0, 0, 0, []
    bots, bot_ok = 0, 0
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            o = {nm for nm, dd in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                 if not frm.inE((x + dd[0], y + dd[1]))}
            if o == {"N"}:
                tops += 1
                q = (x - V[0], y - V[1])
                tq = frm.t(q)
                ts_top.append(tq)
                if 3 - d <= tq <= n + 2 * d - 1:
                    ok_strip += 1
            if o == {"S"}:
                bots += 1
                if 3 - d <= frm.t(p) <= n + 2 * d - 1:
                    bot_ok += 1
    return tuple(w), tops, ok_strip, bots, bot_ok, min(ts_top) if ts_top else None, max(ts_top) if ts_top else None, 3 - d, n + 2 * d - 1

if __name__ == "__main__":
    tot = dict(tops=0, top_minusV_in_strip=0, bots=0, bot_in_strip=0)
    bad = 0
    lo_hi = []
    with Pool(12) as pool:
        for w, tops, ok, bots, bot_ok, tmin, tmax, lo, hi in pool.imap_unordered(run, list(words(4))):
            tot["tops"] += tops; tot["top_minusV_in_strip"] += ok
            tot["bots"] += bots; tot["bot_in_strip"] += bot_ok
            if ok != tops: bad += 1
            lo_hi.append((tmin, tmax))
    print("TOTAL", tot, "words where some pure top minus V misses the strip:", bad, flush=True)
    print("sample t-range of (pure top - V):", sorted(set(lo_hi))[:6], flush=True)
