"""Task 66 (4): on the free H cut (z in E, (z1, z2-1) not in E, t(z) in the H spectrum), check
(a) 0 <= t_p(z) <= N + D with t_p = N z1 - D z2 (the word's odd parent);
(b) even z: l = (z1 + z2)/2 satisfies 1 <= l and 2 l < L (so H_endpoint applies with b = z2);
(c) even z: b = z2 = floor(2 n l / L).
Child (n, d) = (2N + n_q, 2D + d_q), T = d^2 + 2dn - n^2, L = d + n."""
from collections import Counter
from chart_kernel_check import inE
from chart_threshold_check import params
import sheets as S

words = [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]
for w in words:
    n, d, T, eps, U, sig = params(w)
    fr = S.Frame(list(w))
    N, D = fr.N, fr.D
    L = d + n
    cnt = Counter()
    R = 40
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            z = (a, b)
            if not inE(z, n, d, T):
                continue
            t = n * z[0] - d * z[1]
            ev = (z[0] + z[1]) % 2 == 0
            below = (z[0], z[1] - 1)
            if inE(below, n, d, T):
                continue
            hs = (ev and 2 <= t <= L - 2) or ((not ev) and n <= t <= d)
            if not hs:
                continue
            tp = N * z[0] - D * z[1]
            cnt["freeH"] += 1
            cnt["0<=tp<=N+D" if 0 <= tp <= N + D else "TP OUT"] += 1
            if ev:
                l = (z[0] + z[1]) // 2
                cnt["even"] += 1
                cnt["l>=1" if l >= 1 else "l<1"] += 1
                cnt["2l<L" if 2 * l < L else "2l>=L"] += 1
                cnt["b=floor" if z[1] == (2 * n * l) // L else "b!=floor"] += 1
            else:
                cnt["odd"] += 1
    print(w, "N,D,n,d", (N, D, n, d), dict(cnt))
