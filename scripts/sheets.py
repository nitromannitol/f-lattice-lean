"""The two sheets of the standard even field of a word w = p d, from the recursion of proto2.standard (task 46).

F(w) = min(A, C), with Fp = O(p) = quarter(standard(swap p)[0]) + h0 the odd parent field (p the prefix before the last digit
in {1, 2}), frame of w (eps, N, D, nq, dq), W = (1 + eps) // 2, Uq = (dq, nq), Vq = (nq - dq, dq + nq),
lv = (1 - W) Uq, e = Vq + eps Uq, Tq = dq^2 + 2 dq nq - nq^2, ce = (Tq - dq - nq) // 2 + 2 W,
A(z) = Fp(z - lv), C(z) = Fp(z - lv - e) + nq (z0 - lv0) - dq (z1 - lv1) + ce.
"""
import ordinary_tile_check as otc
from odd_donor_jet import Q_of  # noqa: F401  (keeps the proto loaded consistently)

ns = otc.load_proto()
standard, h0, swap, Frame = ns["standard"], ns["h0"], ns["swap"], ns["Frame"]


def sheets(w):
    w = list(w)
    k = max(i for i, x in enumerate(w) if x in (1, 2))
    wp = w[:k]
    Fq = standard(tuple(swap(wp)))[0]
    Fp = lambda x: Fq((-x[1], x[0] - 1)) + h0(*x)
    fr = Frame(w)
    N, D, nq, dq, eps = fr.N, fr.D, fr.nq, fr.dq, fr.eps
    W = (1 + eps) // 2
    Uq = (dq, nq)
    Vq = (nq - dq, dq + nq)
    lv = ((1 - W) * Uq[0], (1 - W) * Uq[1])
    e = (Vq[0] + eps * Uq[0], Vq[1] + eps * Uq[1])
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    A = lambda z: Fp((z[0] - lv[0], z[1] - lv[1]))
    C = lambda z: Fp((z[0] - lv[0] - e[0], z[1] - lv[1] - e[1])) + nq * (z[0] - lv[0]) - dq * (z[1] - lv[1]) + ce
    return A, C, dict(lv=lv, e=e, ce=ce, nq=nq, dq=dq, eps=eps, W=W)


if __name__ == "__main__":
    # F = min(A, C) holds on the closed polygon of the frame only (not on the whole plane); see sheet_table.py for the copies.
    A, C, info = sheets((1, 2))
    print("sheets of (1 2):", info)
