"""Task 66 (2)(c): a canonical chart split. For a non-exit shifted point p: k(p) = 0 if p in E and s(p) < theta(parity),
k(p) = eps if p - eps U in E and s(p) >= theta(parity). Search thresholds theta_even, theta_odd (offsets from T) so that
(a) every non-exit point has a representative, and (b) both ends of every shifted input edge get the same k."""
import sheets as S
from chart_kernel_check import inE, tOK, inputs

def params(w):
    fr = S.Frame(list(w))
    N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
    n, d = 2 * N + nq, 2 * D + dq
    T = d * d + 2 * d * n - n * n
    return n, d, T, eps, (d, n), (eps * 2 * D, eps * 2 * N)

def s_of(p, n, d):
    return (d + n) * p[0] + (d - n) * p[1]

def chart(p, n, d, T, eps, U, theta):
    e_ok = inE(p, n, d, T)
    q = (p[0] - eps * U[0], p[1] - eps * U[1])
    q_ok = inE(q, n, d, T)
    th = theta[(p[0] + p[1]) % 2 == 0]
    s = s_of(p, n, d)
    if e_ok and s < th:
        return 0
    if q_ok and s >= th:
        return eps
    if e_ok:
        return 0
    if q_ok:
        return eps
    return None

def scan(words, R=7):
    res = {}
    for w in words:
        n, d, T, eps, U, sig = params(w)
        pts = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)]
        base = []
        for z in pts:
            if not inE(z, n, d, T):
                continue
            for i in inputs(z):
                if not inE(i, n, d, T):
                    continue
                x = (z[0] + sig[0], z[1] + sig[1]); y = (i[0] + sig[0], i[1] + sig[1])
                if tOK(x, n, d, T) and tOK(y, n, d, T):
                    base.append((x, y))
        for th_e in range(T - 2 * d, T + 2 * n + 4):
            for th_o in range(T - 2 * d, T + 2 * n + 4):
                theta = {True: th_e, False: th_o}
                bad = 0
                for x, y in base:
                    kx = chart(x, n, d, T, eps, U, theta); ky = chart(y, n, d, T, eps, U, theta)
                    if kx is None or ky is None or kx != ky:
                        bad += 1
                res.setdefault((th_e - T, th_o - T), []).append(bad)
    return res

if __name__ == "__main__":
    words = [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]
    res = scan(words)
    good = [k for k, v in res.items() if all(b == 0 for b in v)]
    print("threshold offsets (theta_even - T, theta_odd - T) with zero mismatches on all words:", good[:20], "count", len(good))
    if not good:
        best = sorted(res.items(), key=lambda kv: sum(kv[1]))[:3]
        print("best:", [(k, sum(v)) for k, v in best])
