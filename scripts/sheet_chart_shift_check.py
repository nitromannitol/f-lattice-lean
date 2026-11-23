"""Task 66 (2): numerical checks of the chart identities on the sheets.
(i)  f = Fp (the quarter-turned parent field) is U_p-periodic with constant 0: Fp(z + U_p) - Fp(z) = 0 on a box.
(ii) Psi(z + eta*sigma) - Psi(z) = -2 eta, with sigma = eps U_p, Psi = C - A.
(iii) A(z + eta*sigma) - A(z) = 0 (zero U_p-period of the sheet A).
U_p = (2 D, 2 N) of the word's odd parent; eps = eps of the word."""
import sheets as S

for w in [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1), (1, 2, 1), (2, 1, 3)]:
    A, C, info = S.sheets(w)
    fr = S.Frame(list(w))
    N, D, eps = fr.N, fr.D, fr.eps
    Up = (2 * D, 2 * N)
    Psi = lambda z: C(z) - A(z)
    box = range(-3, 4)
    # Fp is the parent field: A(z) = Fp(z - lv), so Fp(y) = A(y + lv) with lv = info["lv"]
    lv = info["lv"]
    Fp = lambda y: A((y[0] + lv[0], y[1] + lv[1]))
    dF = {Fp((z0 + Up[0], z1 + Up[1])) - Fp((z0, z1)) for z0 in box for z1 in box}
    res = []
    for eta in (1, -1):
        sig = (eta * eps * Up[0], eta * eps * Up[1])
        dPsi = {Psi((z0 + sig[0], z1 + sig[1])) - Psi((z0, z1)) for z0 in box for z1 in box}
        dA = {A((z0 + sig[0], z1 + sig[1])) - A((z0, z1)) for z0 in box for z1 in box}
        res.append((eta, sorted(dPsi)[:3] if len(dPsi) < 4 else "many", sorted(dA)[:3] if len(dA) < 4 else "many"))
    print(w, "eps", eps, "Fp U_p-diff", sorted(dF)[:4], "len", len(dF), " (eta, Psi-shift, A-shift):", res)
