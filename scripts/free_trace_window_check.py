"""Recheck the route windows of ShortPassages on proper children (num >= 3, as child_num_ge_three),
and tabulate each window against the free status of the neighbouring steps of the root.

Uses free_trace_route_check.make (Lean ChildFrame.freeH/freeV, closedPolygon, Nonfree) and the route windows of routes().
Neighbour steps: E=(1,0), N=(0,1), W=(-1,0), S=(0,-1), NE=(1,1)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from free_trace_box_check import children
from free_trace_route_check import make, routes
from collections import Counter

STEPS = {'E': (1, 0), 'N': (0, 1), 'W': (-1, 0), 'S': (0, -1), 'NE': (1, 1)}

def run(dmax, nmin=3):
    tally = Counter(); ex = {}
    for n, d in children(dmax):
        if n < nmin:
            continue
        G = make(n, d); W = 3 * (d + n) + 4
        for name, trace, parity, middles, win in routes(G):
            isfree = G['freeH'] if trace == 'H' else G['freeV']
            for x in range(-W, W + 1):
                for y in range(-W, W + 1):
                    if not isfree(x, y) or (x + y) % 2 != parity:
                        continue
                    w = win(x, y)
                    nf = all(G['nonfree'](x + a, y + b) for a, b in middles)
                    fr = {k: isfree(x + a, y + b) for k, (a, b) in STEPS.items()}
                    fr_s = ','.join(k for k in STEPS if fr[k]) or '-'
                    key = (name, 'window' if w else 'no-window', 'middles-nonfree' if nf else 'MIDDLE-FREE', 'free-steps:' + fr_s)
                    tally[key] += 1
                    ex.setdefault(key, (n, d, (x, y), G['t'](x, y), G['s'](x, y)))
    return tally, ex

if __name__ == '__main__':
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    tally, ex = run(dmax)
    for k in sorted(tally):
        print(k, tally[k], 'e.g.', ex[k])
