"""Task 66 (3'): the input as the exiting end. For c, i in E with i an input of c, and the input's shifted grade below the
lower bound: t(i) - 2 < a(i) - T, a = 2 (i even) or n (i odd). Check the window conclusions of the zero-strip argument:
t(c) + T, t(i) + T in [2, n+1+d] and t(c) - 2 + T, t(i) - 2 + T in [1-d, n+2d-1]. Also record the step t(c) - t(i)."""
from collections import Counter
from chart_kernel_check import inE, tOK, inputs
from chart_threshold_check import params

words = [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]
for w in words:
    n, d, T, eps, U, sig = params(w)
    cnt = Counter()
    R = 30
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            c = (a, b)
            if not inE(c, n, d, T):
                continue
            for i in inputs(c):
                if not inE(i, n, d, T):
                    continue
                ti = n * i[0] - d * i[1]
                tc = n * c[0] - d * c[1]
                ev_i = (i[0] + i[1]) % 2 == 0
                a_i = 2 if ev_i else n
                if not (ti - 2 < a_i - T):
                    continue
                cnt["input-exit"] += 1
                conds = [2 <= tc + T <= n + 1 + d, 2 <= ti + T <= n + 1 + d,
                         1 - d <= tc - 2 + T <= n + 2 * d - 1, 1 - d <= ti - 2 + T <= n + 2 * d - 1]
                cnt["all bounds" if all(conds) else "BOUND FAILS"] += 1
                cnt["step " + str(abs(tc - ti))] += 1
    print(w, "n,d,T", (n, d, T), dict(cnt))
