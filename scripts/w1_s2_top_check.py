import sys
sys.path.insert(0, 'scripts')
from permit_local import standard, Frame, proper_words, win, lap
def add(z, v): return (z[0] + v[0], z[1] + v[1])
def sub(z, v): return (z[0] - v[0], z[1] - v[1])
def arc(z, dirs, A, B):
    a = [z]
    e = [0] + [v for k in range(1, A + B - 1) for v in ([1] if (k + 1) * B // (A + B) != k * B // (A + B) else [0, 0])] + [0]
    for v in e:
        a.append(add(a[-1], dirs[v]))
    return a
def run(w):
    F, _ = standard(w)
    fr = Frame(w)
    n, d, L, T = fr.n, fr.d, fr.L, fr.T
    U, V = (d, n), (n - d, L)
    H = arc((1, 0), [(1, 0), (1, 1)], (d - n) // 2, n)
    vs = arc((0, 0), [(0, 1), (-1, 1)], n, d - n)
    top = [add(p, V) for p in H]
    def inter(z):
        x, y = z
        a, b, c, h = win((x + y) % 2 == 0, n, d)
        t = n * x - d * y; s = L * x + (d - n) * y
        return b - T < t < a and h < s < T + c
    M = 2 * (n + d) + T
    pts = [(x, y) for x in range(-M, M + 1) for y in range(-M, M + 1) if inter((x, y))]
    def near(z, arcpts):
        return any(max(abs(z[0] - p[0]), abs(z[1] - p[1])) <= 1 for p in arcpts)
    col = [z for z in pts if near(z, top)]
    out = dict(word=''.join(map(str, w)), T=T, n=n, d=d, L=L, top=len(col))
    ev = [z for z in col if (z[0] + z[1]) % 2 == 0]
    od = [z for z in col if (z[0] + z[1]) % 2 == 1]
    ty = lambda z: fr.t(sub(z, V))
    if ev:
        out['even_t_y'] = (min(ty(z) for z in ev), max(ty(z) for z in ev), 'claim L-2<t<=2L-2:', L - 2, 2 * L - 2)
    if od:
        out['odd_t_y'] = (min(ty(z) for z in od), max(ty(z) for z in od), 'claim d<t<=n+2d-2:', d, n + 2 * d - 2)
    out['F_y_zero_all'] = all(F(sub(z, V)) == 0 for z in col)
    out['F_y_zero_in_zero_strip'] = all(F(sub(z, V)) == 0 for z in col if 1 - d <= ty(z) <= n + 2 * d - 1)
    out['n_in_zero_strip'] = sum(1 for z in col if 1 - d <= ty(z) <= n + 2 * d - 1)
    out['n_out_strip'] = sum(1 for z in col if not (1 - d <= ty(z) <= n + 2 * d - 1))
    out['F_y_nonzero_out_strip'] = sum(1 for z in col if not (1 - d <= ty(z) <= n + 2 * d - 1) and F(sub(z, V)) != 0)
    return out
for w in [(1,), (1, 2), (1, 3), (2, 1), (3, 1)]:
    print(run(w))
