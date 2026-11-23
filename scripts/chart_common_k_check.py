"""Task 66 (2)(c): is there a common chart k in {0, eps} valid at both ends of every non-exit shifted input edge?
valid0(p) = p in E; validE(p) = p - eps U in E."""
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
            z = (a, b)
            if not inE(z, n, d, T):
                continue
            for i in inputs(z):
                if not inE(i, n, d, T):
                    continue
                x = (z[0] + sig[0], z[1] + sig[1]); y = (i[0] + sig[0], i[1] + sig[1])
                if not (tOK(x, n, d, T) and tOK(y, n, d, T)):
                    cnt["exit"] += 1
                    continue
                def v0(p):
                    return inE(p, n, d, T)
                def vE(p):
                    return inE((p[0] - eps * U[0], p[1] - eps * U[1]), n, d, T)
                common = (v0(x) and v0(y)) or (vE(x) and vE(y))
                cnt["common" if common else "NO COMMON"] += 1
    print(w, dict(cnt))
