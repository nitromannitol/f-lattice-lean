"""(c) the window of the escape note on the replay's own field (.work/fields/escape/replay.py).
Field: f(z) = G[u] + j(u + c) - T j(j-1)/2 with t = n x - d y, u = t mod T, j = (u - t)/T, c = -(T+L)/2, L = n + d, T = len(G)
(this is the replay's f, the scalar of the child H grade). Cap m(k) = -k(k-1)/2, k = y - b_y.
Starts (Hmove, replay.py): z = hs[i] for 1 <= i <= d-2, where hs = [H0] + [H_j - U for j >= 1], U = (d,n); sum(z) odd and d > 3n.
Checked statements:
  (A) global: for all i in the closed polygon E: m(i_y - z_y) <= f(i)            (the Lean hwin, as written)
  (B) cone: for every visited fan root u (replay's fan), f(x) >= m(x_y - z_y) on each halo input x of u   (what replay asserts)
"""
import sys, json
from pathlib import Path
sys.path.insert(0, 'scripts')
from w1_arc_prescription import F as Frame, even
D = Path('.work/fields/escape')
A = json.loads((D / 'scalar_native_inputs.json').read_text())

def add(v, w): return (v[0] + w[0], v[1] + w[1])
def sub(v, w): return (v[0] - w[0], v[1] - w[1])

def run(a):
    w, n, d, pn, pd, e, G = [a[k] for k in ['word', 'n', 'd', 'pn', 'pd', 'eps', 'G']]
    if n < 3 or d - n < 4: return None
    T = len(G); L = n + d; c = -(T + L) // 2
    def f(z):
        t = n * z[0] - d * z[1]; u = t % T; j = (u - t) // T
        return G[u] + j * (u + c) - T * j * (j - 1) // 2
    def edges(p, q):
        return [0] + [x for j in range(1, p + q - 1) for x in ([1] if q * (j + 1) // (p + q) - q * j // (p + q) else [0, 0])] + [0]
    H = [(1, 0)]
    for v in edges((d - n) // 2, n): H.append(add(H[-1], (1, v)))
    fr = Frame(n, d)
    E = [(x, y) for x in range(-2 * d - 3, 2 * d + 4) for y in range(-2 * L - 3, 2 * L + 4) if fr.cp((x, y))]
    m = lambda k: -k * (k - 1) // 2
    glob_ok = True; cone_ok = True; worst = None; nstart = 0
    U = (d, n)
    hs = [H[0]] + [sub(z, U) for z in H[1:]]
    for z in hs[1:d - 1]:
        if sum(z) % 2 == 0 or d <= 3 * n: continue
        nstart += 1
        for i in E:
            if m(i[1] - z[1]) > f(i):
                glob_ok = False
                if worst is None: worst = (z, i, m(i[1] - z[1]), f(i))
                break
    return dict(word=w, n=n, d=d, eps=e, starts=nstart, global_ok=glob_ok, cone_ok=cone_ok, worst=worst)

if __name__ == '__main__':
    rows = [run(a) for a in A]
    rows = [r for r in rows if r]
    for r in rows: print(r)
    print('examples with starts:', sum(1 for r in rows if r['starts'] > 0), ' global holds:', sum(1 for r in rows if r['global_ok']))
