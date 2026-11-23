import sheets as S
from chart_kernel_check import inE, tOK, inputs
w = (1,)
fr = S.Frame(list(w))
N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
n, d = 2 * N + nq, 2 * D + dq
T = d * d + 2 * d * n - n * n
U = (d, n); sig = (eps * 2 * D, eps * 2 * N)
print("word", w, "child n,d,T", n, d, T, "eps", eps, "sigma", sig, "U", U)
overlap = 0
for a in range(-6, 7):
    for b in range(-6, 7):
        z = (a, b)
        if not inE(z, n, d, T):
            continue
        for i in inputs(z):
            if not inE(i, n, d, T):
                continue
            x = (z[0] + sig[0], z[1] + sig[1]); y = (i[0] + sig[0], i[1] + sig[1])
            if not (tOK(x, n, d, T) and tOK(y, n, d, T)):
                continue
            def kind(p):
                a0 = inE(p, n, d, T); q = (p[0] - eps * U[0], p[1] - eps * U[1]); a1 = inE(q, n, d, T)
                return a0, a1
            kx, ky = kind(x), kind(y)
            if (kx[0] and kx[1]) or (ky[0] and ky[1]):
                overlap += 1
            if kx[0] != ky[0]:
                print("z", z, "i", i, "x", x, "in E", kx, "y", y, "in E", ky, "t(x),t(y)", n*x[0]-d*x[1], n*y[0]-d*y[1], "s(x),s(y)", (d+n)*x[0]+(d-n)*x[1], (d+n)*y[0]+(d-n)*y[1])
print("overlap count", overlap, "T", T)
