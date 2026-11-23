"""Task 65 (1)/(2): is the sheet minimum M = min(A, C) globally periodic on the word's child lattice?
U = (den, num) and V = (num - den, num + den) of the word's child; tGrade(z) = num z1 - den z2.
Prints, for a box, whether M(z+U) - M(z) is constant and whether M(z+V) - M(z) + s * tGrade(z) is constant (s = +-1)."""
import sheets as S

for w in [(1,), (2,), (1, 2), (2, 1), (1, 3, 2), (3, 1, 2), (1, 1, 2), (2, 2, 1)]:
    A, C, info = S.sheets(w)
    M = lambda z: min(A(z), C(z))
    fr = S.Frame(list(w))
    Nn, Dd, nq, dq = fr.N, fr.D, fr.nq, fr.dq
    den = 2 * Dd + dq
    num = 2 * Nn + nq
    U = (den, num)
    V = (num - den, num + den)
    tg = lambda z: num * z[0] - den * z[1]
    box = range(-2, 3)
    dU = {M((z0 + U[0], z1 + U[1])) - M((z0, z1)) for z0 in box for z1 in box}
    dV = {M((z0 + V[0], z1 + V[1])) - M((z0, z1)) + s * tg((z0, z1)) for z0 in box for z1 in box for s in [1]}
    dVm = {M((z0 + V[0], z1 + V[1])) - M((z0, z1)) - tg((z0, z1)) for z0 in box for z1 in box}
    print(w, "U-diff const:", len(dU) == 1, sorted(dU)[:3], " V+tg const:", len(dV) == 1, " V-tg const:", len(dVm) == 1)
