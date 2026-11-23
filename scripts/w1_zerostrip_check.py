"""Task 59 numerics: zeroStripInterval and zeroEvenLine at u, against the packet strips.

u a proper even word, F = standard(u), h = F - h0. Child (n,d), parent N/D, L = d+n, T as usual.
zeroStripInterval: quarterTurn F (x) = F(Zx) + h0(x) = 0 on 1-D <= t_p(x) <= N+2D-1, with Zx = (-x2, x1-1).
With y = Zx: t_p(x) = D y1 + N y2 + N, and h0(x) = -h0(y), so the claim is h(y) = 0 on the band
  1-D-N <= D y1 + N y2 <= 2D-1.
zeroEvenLine: h(y) = 0 for y odd (x even) with D y1 + N y2 = -D-N.
Packet strips (HasStrips): h = 0 on the t-band of F? no: F = 0 on t in [1-d, n+2d-1]; F = h0 (i.e. h = 0) on s in [1-2d, 2L-1].
Question: is h a function of (s, parity) (V invariance), and where do the band's s-values lie relative to the strips?
"""
import itertools, sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, h0, parents

def run(w, B=40):
    (N, D), (nq, dq) = parents(w)
    fr = Frame(w)
    n, d = fr.n, fr.d
    L = d + n
    G, _ = standard(tuple(w))
    h = lambda y: G(y) - h0(*y)
    band = []
    zeroEven = []
    for y1 in range(-B, B + 1):
        for y2 in range(-B, B + 1):
            f = D * y1 + N * y2
            if 1 - D - N <= f <= 2 * D - 1:
                band.append((y1, y2))
            if f == -D - N and (y1 + y2) % 2 == 1:
                zeroEven.append((y1, y2))
    bad_band = [y for y in band if h(y) != 0]
    bad_even = [y for y in zeroEven if h(y) != 0]
    s_by_par = {0: set(), 1: set()}
    for y in band:
        s_by_par[(y[0] + y[1]) % 2].add(L * y[0] + (d - n) * y[1])
    # is h a function of (s, parity)?
    seen = {}
    conflict = 0
    for y1 in range(-12, 13):
        for y2 in range(-12, 13):
            key = (L * y1 + (d - n) * y2, (y1 + y2) % 2)
            v = h((y1, y2))
            if key in seen and seen[key] != v:
                conflict += 1
            seen.setdefault(key, v)
    return dict(n=n, d=d, N=N, D=D, band=len(band), bad_band=len(bad_band), zeroEven=len(zeroEven),
                bad_even=len(bad_even), conflict=conflict,
                s_even=(min(s_by_par[0]), max(s_by_par[0])) if s_by_par[0] else None,
                s_odd=(min(s_by_par[1]), max(s_by_par[1])) if s_by_par[1] else None,
                ordinary=(1 - 2 * d, 2 * L - 1), oddext=(2 - 3 * d + n, 3 * d + n - 2))

if __name__ == '__main__':
    for L_ in (1, 2):
        for w in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in w) or all(x == 2 for x in w):
                continue
            if Frame(w).d > 30:
                continue
            r = run(w)
            print(''.join(map(str, w)), r, flush=True)
