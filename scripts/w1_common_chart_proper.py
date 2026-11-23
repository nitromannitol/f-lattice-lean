"""Task 68 numerics: the common-chart claim of SHORT_SLIP_COMMON_CHART under its own hypotheses (proper child, both ends of an edge in E,
the t-support of ChartCommon.common_chart_option). Frames: child (n,d) = (2N + nq, 2D + dq) with the odd parent N/D and even sibling nq/dq,
n >= 3, d >= n + 2, eps = N d - D n = +-1. Claim for each edge i -> c with i, c in E and the support conditions:
  (c + sigma, i + sigma in E) or (c - eps (dq, nq), i - eps (dq, nq) in E),  sigma = (2 eps D, 2 eps N).
"""
from itertools import product
from collections import Counter


def inE(x, n, d):
    T = d * d + 2 * d * n - n * n
    L = d + n
    t = n * x[0] - d * x[1]
    s = L * x[0] + (d - n) * x[1]
    if (x[0] + x[1]) % 2 == 0:
        return 2 - T <= t <= L - 2 and 0 <= s <= T + 2 * n
    return n - T <= t <= d and 2 - d + n <= s <= T + L - 2


def frames(maxv=10):
    for N, D, nq, dq in product(range(1, maxv), range(2, maxv), range(1, maxv), range(1, maxv)):
        if N >= D:
            continue
        if (N + D) % 2 == 0 or (nq + dq) % 2 != 0:   # odd parent N/D, even sibling nq/dq (parity validity)
            continue
        n, d = 2 * N + nq, 2 * D + dq
        if n < 3 or d < n + 2 or (n + d) % 2 != 0:   # proper child, even child
            continue
        eps = N * d - D * n
        if eps not in (1, -1):
            continue
        yield (N, D, nq, dq, n, d, eps)


def run(maxv=10):
    stats = Counter()
    fails = []
    for (N, D, nq, dq, n, d, eps) in frames(maxv):
        T = d * d + 2 * d * n - n * n
        L = d + n
        sig = (2 * eps * D, 2 * eps * N)
        sg = (eps * dq, eps * nq)
        M = 3 * (d + n) + 4
        for x in range(-M, M + 1):
            for y in range(-M, M + 1):
                c = (x, y)
                if not inE(c, n, d):
                    continue
                even_c = (c[0] + c[1]) % 2 == 0
                for i in ((x - 1, y), (x + 1, y)) if even_c else ((x, y - 1), (x, y + 1)):
                    if not inE(i, n, d):
                        continue
                    tc = n * c[0] - d * c[1]
                    ti = n * i[0] - d * i[1]
                    even_i = (i[0] + i[1]) % 2 == 0
                    lo_c = (2 if even_c else n) - T
                    lo_i = (2 if even_i else n) - T
                    if not (tc - 2 >= lo_c and ti - 2 >= lo_i):
                        stats['support_excluded'] += 1
                        continue
                    stats['tested'] += 1
                    up = inE((c[0] + sig[0], c[1] + sig[1]), n, d) and inE((i[0] + sig[0], i[1] + sig[1]), n, d)
                    dn = inE((c[0] - sg[0], c[1] - sg[1]), n, d) and inE((i[0] - sg[0], i[1] - sg[1]), n, d)
                    if up:
                        stats['option_plus'] += 1
                    elif dn:
                        stats['option_minus'] += 1
                    else:
                        stats['FAIL'] += 1
                        if len(fails) < 5:
                            fails.append((N, D, nq, dq, n, d, eps, c, i))
    return stats, fails


if __name__ == '__main__':
    stats, fails = run()
    print('frames: proper, n>=3, d>=n+2, eps=+-1')
    print(dict(stats))
    print('first failures:', fails)
    print('frames checked:', sum(1 for _ in frames()))
