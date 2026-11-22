from multiprocessing import Pool
import permit_local as pl
from exact_quotient import words
from arc_inputs116 import bbox

def run(w):
    w = list(w)
    frm = pl.Frame(w)
    n, d, T, L = frm.n, frm.d, frm.T, frm.L
    N, Dd = pl.parents(w)[0]
    sig = (2 * frm.eps * Dd, 2 * frm.eps * N)
    U, V, I = (d, n), (n - d, n + d), (1, -1)
    c = (U[0] + V[0] + I[0], U[1] + V[1] + I[1])
    x0, x1, y0, y1 = bbox(frm)
    E = frm.inE
    def cls(p):
        o = {nm for nm, dd in (("N", (0, 1)), ("S", (0, -1)), ("E", (1, 0)), ("W", (-1, 0)))
             if not E((p[0] + dd[0], p[1] + dd[1]))}
        if not o: return "int"
        if o == {"S"}: return "bot"
        if o == {"N"}: return "top"
        return "other"
    def rep_classes(q):
        even = (q[0] + q[1]) % 2 == 0
        lo, hi = (2 - T, L - 2) if even else (n - T, d)
        if not (lo <= frm.t(q) <= hi):
            return None
        slo, shi = (0, T + 2 * n) if even else (2 - d + n, T + L - 2)
        sq = frm.sg(q)
        kc = -((sq - slo) // T)
        cl = set()
        for k in range(kc - 2, kc + 3):
            r = (q[0] + k * d, q[1] + k * n)
            if E(r):
                cl.add(cls(r))
        return cl
    def forced(u, refl):
        cands = []
        for j in (-1, 0, 1):
            q = (u[0] + j * V[0], u[1] + j * V[1])
            cl = rep_classes(q)
            if not cl: continue
            for k_c in cl:
                if not refl:
                    # D(u) = D(r) - 2j
                    if (k_c == "int" and j == 0) or (k_c == "bot" and j in (0, -1)) or (k_c == "top" and j in (0, 1)):
                        return True
                else:
                    # D(u) = 2 - D(r) + 2j
                    if (k_c == "int" and j == 0) or (k_c == "bot" and j in (0, -1)) or (k_c == "top" and j in (0, 1)):
                        return True
        return False
    tot = cov = direct = refl_only = 0
    bad = []
    for x in range(x0, x1 + 1):
        for y in range(y0, y1 + 1):
            p = (x, y)
            if not E(p): continue
            even = (x + y) % 2 == 0
            ins = [(x - 1, y), (x + 1, y)] if even else [(x, y - 1), (x, y + 1)]
            for u in ins:
                if E(u): continue
                tot += 1
                a = forced(u, False)
                r_ = (c[0] - sig[0] - u[0], c[1] - sig[1] - u[1])
                b = forced(r_, True)
                if a or b:
                    cov += 1
                    if a: direct += 1
                    elif b: refl_only += 1
                else:
                    side = ("W" if u[0] < x else "E") if u[1] == y else ("S" if u[1] < y else "N")
                    bad.append((side, "even" if (u[0]+u[1]) % 2 == 0 else "odd"))
    return tuple(w), tot, cov, direct, refl_only, bad

if __name__ == "__main__":
    tot = dict(outside=0, covered=0, direct=0, reflect_only=0, uncovered=0)
    from collections import Counter
    cnt = Counter()
    with Pool(12) as pool:
        for w, t, c_, dr, ro, bd in pool.imap_unordered(run, list(words(4))):
            tot["outside"] += t; tot["covered"] += c_; tot["direct"] += dr; tot["reflect_only"] += ro; tot["uncovered"] += len(bd)
            cnt.update(bd)
    print("TOTAL", tot, flush=True)
    print("UNCOVERED BY (side, parity of input):", dict(cnt), flush=True)
