"""Task 66 (4): odd free H points. Identity (checked symbolically): L * tp = Lp * t + eps * m, with t = n z1 - d z2,
m = z1 + z2, tp = N z1 - D z2, L = d + n, Lp = D + N. Check ranges of m and t on the odd free H cut."""
from collections import Counter
from chart_kernel_check import inE
from chart_threshold_check import params
import sheets as S
words = [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]
for w in words:
    n, d, T, eps, U, sig = params(w)
    fr = S.Frame(list(w)); N, D = fr.N, fr.D
    L = d + n; Lp = D + N
    cnt = Counter(); ms = []
    R = 40
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            z = (a, b)
            if (z[0] + z[1]) % 2 == 0 or not inE(z, n, d, T):
                continue
            if inE((z[0], z[1] - 1), n, d, T):
                continue
            t = n * z[0] - d * z[1]
            if not (n <= t <= d):
                continue
            m = z[0] + z[1]; tp = N * z[0] - D * z[1]
            assert L * tp == Lp * t + eps * m
            ms.append(m)
            cnt["odd freeH"] += 1
            cnt["0<=tp<=Lp" if 0 <= tp <= Lp else "TP OUT"] += 1
            cnt["1<=m<=L-1" if 1 <= m <= L - 1 else "m OUT"] += 1
    print(w, "eps", eps, "n,d,N,D", (n, d, N, D), "m range", (min(ms), max(ms)) if ms else None, dict(cnt))
