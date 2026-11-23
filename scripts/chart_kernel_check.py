"""Task 66 (2)(c): the chart representative of a shifted point. Child (n, d) = (2N + n_q, 2D + d_q), T = d^2 + 2dn - n^2,
t(x) = n x1 - d x2, s(x) = (d+n) x1 + (d-n) x2, U = (d, n), sigma = eps U_p with U_p = (2D, 2N), eta = +1.
E (closedPolygon): even: 2-T <= t <= d+n-2, 0 <= s <= T+2n; odd: n-T <= t <= d, 2-d+n <= s <= T+d+n-2.
For a shifted point x (non-exit: t(x) in the parity's t-range) classify: k=0 if x in E; k=eps if x - eps*U in E; else 'none'.
Check the same k at both ends of an input edge (z, i) with z, i in E (i input of z)."""
from collections import Counter
import sheets as S

def inE(x, n, d, T):
    t = n * x[0] - d * x[1]
    s = (d + n) * x[0] + (d - n) * x[1]
    if (x[0] + x[1]) % 2 == 0:
        return 2 - T <= t <= d + n - 2 and 0 <= s <= T + 2 * n
    return n - T <= t <= d and 2 - d + n <= s <= T + d + n - 2

def tOK(x, n, d, T):
    t = n * x[0] - d * x[1]
    if (x[0] + x[1]) % 2 == 0:
        return 2 - T <= t <= d + n - 2
    return n - T <= t <= d

def inputs(z):
    if (z[0] + z[1]) % 2 == 0:
        return [(z[0] - 1, z[1]), (z[0] + 1, z[1])]
    return [(z[0], z[1] - 1), (z[0], z[1] + 1)]

def run(w, R=6):
    fr = S.Frame(list(w))
    N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
    n, d = 2 * N + nq, 2 * D + dq
    T = d * d + 2 * d * n - n * n
    U = (d, n)
    sig = (eps * 2 * D, eps * 2 * N)
    cnt = Counter()
    pts = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)]
    for z in pts:
        if not inE(z, n, d, T):
            continue
        for i in inputs(z):
            if not inE(i, n, d, T):
                continue
            x = (z[0] + sig[0], z[1] + sig[1])
            y = (i[0] + sig[0], i[1] + sig[1])
            if not (tOK(x, n, d, T) and tOK(y, n, d, T)):
                cnt["exit"] += 1
                continue
            def kind(p):
                if inE(p, n, d, T):
                    return 0
                q = (p[0] - eps * U[0], p[1] - eps * U[1])
                if inE(q, n, d, T):
                    return eps
                return "none"
            kx, ky = kind(x), kind(y)
            cnt[(str(kx), str(ky))] += 1
    return cnt

if __name__ == "__main__":
    for w in [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]:
        print(w, dict(run(w)))
