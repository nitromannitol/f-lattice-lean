"""For each route theorem of ShortPassages, test on every free root of the trace and parity it takes:
  the middles are Nonfree (no deck translate lies in freeH or freeV), and whether the theorem's root windows hold.
Definitions mirror free_trace_box_check.py (Lean: ChildFrame.freeH/freeV, closedPolygon, NonfreeBridge.Nonfree, span = iK + jV,
K = (d, n), V = (n-d, n+d))."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from free_trace_box_check import children
from collections import Counter

def make(n, d):
    L, c = d + n, d - n
    T = d * d + 2 * d * n - n * n
    t_of = lambda x, y: n * x - d * y
    s_of = lambda x, y: L * x + c * y
    def inE(x, y):
        t, s = t_of(x, y), s_of(x, y)
        if (x + y) % 2 == 0:
            return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
        return n - T <= t <= d and 2 - d + n <= s <= T + d + n - 2
    def hS(t): return (t % 2 == 0 and 2 <= t <= L - 2) or (t % 2 == 1 and n <= t <= d)
    def vS(s): return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= L - 2))
    def freeH(x, y): return inE(x, y) and not inE(x, y - 1) and hS(t_of(x, y))
    def freeV(x, y): return inE(x, y) and not inE(x - 1, y) and vS(s_of(x, y))
    K, V = (d, n), (n - d, n + d)
    def nonfree(x, y):
        for i in range(-4, 5):
            for j in range(-4, 5):
                a, b = x + i * K[0] + j * V[0], y + i * K[1] + j * V[1]
                if freeH(a, b) or freeV(a, b):
                    return False
        return True
    return dict(n=n, d=d, L=L, c=c, T=T, t=t_of, s=s_of, inE=inE, freeH=freeH, freeV=freeV, nonfree=nonfree)

def routes(G):
    n, d, L, c, T, t, s = G['n'], G['d'], G['L'], G['c'], G['T'], G['t'], G['s']
    out = []
    # (name, trace, parity wanted, middles, windows(x,y))
    def H_EN(x, y):
        return (c + 2 <= t(x, y)) and (s(x, y) < T + 2 - 2 * d)
    def H_NES(x, y):
        return (n + 2 <= t(x, y) <= d - 2) and (2 * n - 2 < s(x, y) < T + 2 - 3 * d + n)
    def V_NW(x, y):
        return (2 * n + 2 - c <= s(x, y) <= L - 2) and (L - 1 - T + d < t(x, y) < d)
    def V_WNE(x, y):
        return (2 <= s(x, y) <= 2 * n - 2) and (2 * L - 1 - T < t(x, y) < n)
    out.append(('H_EN', 'H', 0, [(1, 0)], H_EN))
    out.append(('H_NES', 'H', 1, [(0, 1), (1, 1)], H_NES))
    out.append(('V_NW', 'V', 1, [(0, 1)], V_NW))
    out.append(('V_WNE', 'V', 0, [(-1, 0), (-1, 1)], V_WNE))
    return out

def run(dmax):
    tally = Counter(); examples = {}
    R = None
    for n, d in children(dmax):
        G = make(n, d)
        L, T = G['L'], G['T']
        W = 3 * (d + n) + 4
        for name, trace, parity, middles, win in routes(G):
            isfree = G['freeH'] if trace == 'H' else G['freeV']
            for x in range(-W, W + 1):
                for y in range(-W, W + 1):
                    if not isfree(x, y) or (x + y) % 2 != parity:
                        continue
                    ok_w = win(x, y)
                    nf = all(G['nonfree'](x + a, y + b) for a, b in middles)
                    key = (name, 'window' if ok_w else 'no-window', 'nonfree' if nf else 'FREE-MIDDLE')
                    tally[key] += 1
                    if key not in examples:
                        examples[key] = (n, d, (x, y), G['t'](x, y), G['s'](x, y))
    return tally, examples

if __name__ == '__main__':
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    tally, ex = run(dmax)
    for k in sorted(tally):
        print(k, tally[k], 'e.g. (n,d,root,t,s)=', ex[k])
