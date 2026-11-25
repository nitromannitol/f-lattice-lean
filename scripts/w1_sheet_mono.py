"""Numerical check of SheetMono on the replay's scalar field f (the escape note's field, .work/fields/escape/replay.py).
f depends only on t = n x - d y: f = G[u] + j(u+c) - T j(j-1)/2, u = t mod T, j = (u-t)/T, c = -(T+L)/2, L = n+d.
SheetMono (even sheet, t-monotone in the negative range): for even sites p, q with t(p) <= t(q) <= 0, f(p) <= f(q).
This script reports, per entry, the number of violating pairs over a window of even sites."""
import json, sys
from pathlib import Path

D = Path('.work/fields/escape')
A = json.loads((D / 'scalar_native_inputs.json').read_text())

def run(a, R=40):
    n, d, G = a['n'], a['d'], a['G']
    if n < 3 or d - n < 4:
        return None
    T = len(G); L = n + d; c = -(T + L) // 2
    def f(t):
        u = t % T; j = (u - t) // T
        return G[u] + j * (u + c) - T * j * (j - 1) // 2
    vals = {}
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            if (x + y) % 2 != 0:
                continue
            t = n * x - d * y
            if t <= 0:
                vals.setdefault(t, f(t))
    ts = sorted(vals)
    viol = 0; worst = None
    for i in range(len(ts) - 1):
        if vals[ts[i]] > vals[ts[i + 1]]:
            viol += 1
            if worst is None:
                worst = (ts[i], ts[i + 1], vals[ts[i]], vals[ts[i + 1]])
    return len(ts), viol, worst

if __name__ == '__main__':
    tot = 0
    for a in A:
        r = run(a)
        if r is None:
            continue
        cnt, viol, worst = r
        tot += viol
        print(a['word'] or '(empty)', 'n', a['n'], 'd', a['d'], 'even t-values <= 0:', cnt, 'violations:', viol, worst)
    print('total violations', tot)
