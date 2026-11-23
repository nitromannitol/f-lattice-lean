"""Task 74 (2): the two odd-seed identities of the fixer's Q14 at the translated even point, over all integer parameters with
p = (D, N) odd parent, q = (e, r) even sibling, U = 2p + q, eps = N e - D r in {1, -1}, W = (1 + eps)/2.
h0 = harmonicGrid. Identities (fixer, Q14):
  I1: h0(z) + t_p(q + k) - (B + R)/2 + (1 - W) J = 0,
  I2: h0(z) + h0(y) + W J = 0,
with z = (R - 1, b + 1) + (1 - W)(e + r, e - r), Y = Z z + U, Z(x,y) = (-y, x - 1),
J = t_q(Y - (1 - W) q) + (e^2 + 2 e r - r^2 - e - r)/2 + 2 W, y = V_p - eps V_q + k, k = (-1, -2),
B = D^2 + 2DN - N^2, R = D + N, b = D - N, V_h = (h_y - h_x, h_x + h_y), t_p(x) = N x1 - D x2, t_q(x) = r x1 - e x2.
"""
import itertools


def h0(x):
    x1, x2 = x
    return (x1 * x1 + 2 * x1 * x2 - x2 * x2 - 2 * x2 - ((x1 + x2) % 2)) // 4


def check(D, N, e, r):
    eps = N * e - D * r
    if eps not in (1, -1):
        return None
    W = (1 + eps) // 2
    B = D * D + 2 * D * N - N * N
    R = D + N
    b = D - N
    k = (-1, -2)
    z = (R - 1 + (1 - W) * (e + r), b + 1 + (1 - W) * (e - r))
    U = (2 * D + e, 2 * N + r)
    Zz = (-z[1], z[0] - 1)
    Y = (Zz[0] + U[0], Zz[1] + U[1])
    def tq(x): return r * x[0] - e * x[1]
    def tp(x): return N * x[0] - D * x[1]
    J = tq((Y[0] - (1 - W) * e, Y[1] - (1 - W) * r)) + (e * e + 2 * e * r - r * r - e - r) // 2 + 2 * W
    v = (e + k[0], r + k[1])
    assert (e * e + 2 * e * r - r * r - e - r) % 2 == 0
    assert (B + R) % 2 == 0
    I1 = h0(z) + tp(v) - (B + R) // 2 + (1 - W) * J
    Vp = (N - D, D + N)
    Vq = (r - e, e + r)
    y = (Vp[0] - eps * Vq[0] + k[0], Vp[1] - eps * Vq[1] + k[1])
    I2 = h0(z) + h0(y) + W * J
    parity_z = (z[0] + z[1]) % 2
    parity_y = (y[0] + y[1]) % 2
    return I1, I2, parity_z, parity_y


if __name__ == "__main__":
    from collections import Counter
    st = Counter()
    for D, N, e, r in itertools.product(range(-6, 7), repeat=4):
        res = check(D, N, e, r)
        if res is None:
            continue
        I1, I2, pz, py = res
        if (D + N) % 2 == 0 or (e + r) % 2 != 0:
            st['outside_parity'] += 1
            continue
        st[('I1=0', I1 == 0)] += 1
        st[('I2=0', I2 == 0)] += 1
        st[('z even', pz == 0)] += 1
        st[('y odd', py == 1)] += 1
    print(dict(st))
