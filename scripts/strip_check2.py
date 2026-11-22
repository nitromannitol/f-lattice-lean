from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    n, d, L, T = frm.n, frm.d, frm.L, frm.T
    tsig = frm.t(sig)
    x0, x1, y0, y1 = bbox(frm)
    bot_all, top_all = set(), set()
    pure_b, pure_t = set(), set()
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not frm.inE(p):
                continue
            o = {nm for nm, dd in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
                 if not frm.inE((x + dd[0], y + dd[1]))}
            if "S" in o: bot_all.add(p)
            if "N" in o: top_all.add(p)
            if o == {"S"}: pure_b.add(p)
            if o == {"N"}: pure_t.add(p)
    shift_ok = 0
    for p in pure_b:
        q = (p[0] + sig[0], p[1] + sig[1])
        if 1 - d <= frm.t(q) <= n + 2 * d - 1:
            shift_ok += 1
    V = (n - d, n + d)
    bV = {(p[0] + V[0], p[1] + V[1]) for p in bot_all}
    return tuple(w), dict(tsig=tsig, pure_b=len(pure_b), shift_in_zero=shift_ok, top_all=len(top_all),
                          botV_eq_top_all=int(bV == top_all), bot_all=len(bot_all),
                          botV_inter_top=len(bV & top_all), frac=len(bV & top_all))

if __name__ == "__main__":
    ws = list(words(4))
    rows = []
    with Pool(12) as pool:
        for w, r in pool.imap_unordered(run, ws):
            rows.append((w, r))
    print("tsig values", sorted({r['tsig'] for _, r in rows}), flush=True)
    print("pure_b", sum(r['pure_b'] for _, r in rows), "shift_in_zero", sum(r['shift_in_zero'] for _, r in rows), flush=True)
    print("botV_eq_top_all words", sum(r['botV_eq_top_all'] for _, r in rows), "of", len(rows), flush=True)
    for w, r in sorted(rows, key=lambda x: (len(x[0]), x[0]))[:4]:
        print("WORD", w, r, flush=True)
