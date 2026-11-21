"""Numerical check of PermitLocal for the two (I3) permit relations on the quarter-turned parent Fp.

Model (from ~/rwc-wc/fl/proto/proto2.py, extended with the Lean definitions):
  standard(w): the field of a word (B1 base, periodized tile, sheets), as in proto2.
  Fp(x) = G(-x2, x1 - 1) + h0(x), with G = standard(conjWord w), conjWord w = swap(oddBirthPrefix w).
  Xi(x) = earlierChainPrice G P old new (-x2, x1 - 1), with P = odd parent of conjWord w (earlierChainPrice in
          Farey/EarlierChain.lean: earlier(s) - earlier(s + earlierChainShift P old new) + old * P.transverseGrade(s)).
  permitsA(c, i) := Xi i <= Xi c            (the A-type relation of (I3))
  permitsC(c, i) := Xi (c + off) <= Xi (i + off)   (the C-type relation, off = sheetOffset of the frame of w)
  PermitLocal(Fp, p): laplacian Fp c = -1 -> p c neg and p c pos;  laplacian Fp c = 0 -> p c neg or p c pos.
"""
import functools
import itertools
import sys

sys.setrecursionlimit(100000)


def h0(x, y):
    return (x * x + 2 * x * y - y * y - 2 * y - ((x + y) % 2)) // 4


def step(P, d):
    (oN, oD), (eN, eD) = P
    co = (oN + eN, oD + eD)
    ce = (2 * oN + eN, 2 * oD + eD)
    return {1: (co, ce), 2: (co, (eN, eD)), 3: ((oN, oD), ce)}[d]


def parents(w):
    P = ((0, 1), (1, 1))
    for d in w:
        P = step(P, d)
    return P


def win(ev, n, d):
    L = d + n
    return (2, L - 2, 0, 2 * n) if ev else (n, d, 2 - d + n, L - 2)


class Frame:
    def __init__(s, w):
        (N, D), (nq, dq) = parents(w)
        s.N, s.D, s.nq, s.dq = N, D, nq, dq
        s.n, s.d = 2 * N + nq, 2 * D + dq
        n, d = s.n, s.d
        s.T = d * d + 2 * d * n - n * n
        s.L = d + n
        s.eps = N * d - D * n
        s.U = (d, n)
        s.V = (n - d, n + d)

    def t(s, z):
        return s.n * z[0] - s.d * z[1]

    def sg(s, z):
        return s.L * z[0] + (s.d - s.n) * z[1]

    def inE(s, z):
        a, b, c, h = win((z[0] + z[1]) % 2 == 0, s.n, s.d)
        return a - s.T <= s.t(z) <= b and c <= s.sg(z) <= s.T + h

    def periodize(s, M, cU, cV):
        T = s.T
        U, V = s.U, s.V

        @functools.lru_cache(None)
        def F(z):
            a, b, c, h = win((z[0] + z[1]) % 2 == 0, s.n, s.d)
            j = -((s.t(z) - (a - T)) // T)
            i = (s.sg(z) - c) // T
            y = (z[0] - i * U[0] - j * V[0], z[1] - i * U[1] - j * V[1])
            assert s.inE(y), (z, y)
            tg = s.d * y[1] - s.n * y[0]
            return M(y) + i * cU + j * (cV - tg) - T * (j * (j - 1) // 2)

        return F


def B1(d):
    tile = {}
    for x1 in range(2 - d, d + 1):
        for x2 in range(0, d + 2):
            if 1 <= x1 + x2 <= d + 2:
                tile[(x1, x2)] = -(x2 * (x2 - 1) // 2) + min(x1 - 1, 0)
    for c in [(0, 0), (2, d + 1)]:
        tile[c] = -(c[1] * (c[1] - 1) // 2) + min(c[0] - 1, 0) + 1
    fr = Frame([3] * ((d - 3) // 2))
    assert (fr.n, fr.d) == (1, d)
    return fr.periodize(lambda y: tile[y], 0, -((d + 1) * d // 2) - d)


def swap(w):
    return [{1: 1, 2: 3, 3: 2}[x] for x in w]


def odd_birth_prefix(w):
    # the Lean oddBirthPrefix: drop the trailing threes, then the last non-three digit
    w = list(w)
    k = len(w)
    while k > 0 and w[k - 1] == 3:
        k -= 1
    return w[: max(k - 1, 0)]


@functools.lru_cache(None)
def standard(w):
    w = list(w)
    if all(x == 3 for x in w):
        return B1(2 * len(w) + 3), None
    wp = odd_birth_prefix(w)
    Fq, _ = standard(tuple(swap(wp)))
    Fp = lambda x: Fq((-x[1], x[0] - 1)) + h0(*x)
    fr = Frame(w)
    N, D, nq, dq = fr.N, fr.D, fr.nq, fr.dq
    eps = fr.eps
    W = (1 + eps) // 2
    Uq = (dq, nq)
    Vq = (nq - dq, dq + nq)
    lv = ((1 - W) * Uq[0], (1 - W) * Uq[1])
    e = (Vq[0] + eps * Uq[0], Vq[1] + eps * Uq[1])
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    A = lambda z: Fp((z[0] - lv[0], z[1] - lv[1]))
    C = lambda z: Fp((z[0] - lv[0] - e[0], z[1] - lv[1] - e[1])) + nq * (z[0] - lv[0]) - dq * (z[1] - lv[1]) + ce
    M = lambda z: min(A(z), C(z))
    kap = (fr.L - fr.T) // 2
    R = (fr.U[0] + fr.V[0] + 1, fr.U[1] + fr.V[1] - 1)
    Vp1 = (fr.V[0] + 1, fr.V[1] - 1)
    cU = h0(*Vp1) - fr.t(Vp1) + kap
    cV = kap - fr.t(R) + fr.t(fr.V)
    return fr.periodize(M, cU, cV), (fr, M, R, kap)


def earlier_chain_price(G, P, old, new, site):
    """Farey/EarlierChain.lean: earlierChainPrice G P old new site."""
    pN, pD = P
    shift = (2 * new * old * pD - old * (pN - pD), 2 * new * old * pN - old * (pN + pD))
    tg = pD * site[1] - pN * site[0]
    x = (site[0] + shift[0], site[1] + shift[1])
    return G(site) - G(x) + old * tg


def model(w):
    """Return (Fp, Xi, off) for a word w (tuple of digits 1,2,3)."""
    conj = tuple(swap(odd_birth_prefix(list(w))))
    G, _ = standard(conj)
    P = parents(list(conj))[0]
    old = Frame(odd_birth_prefix(list(w))).eps
    new = Frame(list(w)).eps
    Fp = lambda x: G((-x[1], x[0] - 1)) + h0(*x)
    Xi = lambda x: earlier_chain_price(G, P, old, new, (-x[1], x[0] - 1))
    fr = Frame(list(w))
    (eN, eD) = parents(list(w))[1]
    kernel = (eD, eN)
    transverse = (eN - eD, eN + eD)
    off = (transverse[0] + fr.eps * kernel[0], transverse[1] + fr.eps * kernel[1])
    return Fp, Xi, off


def neighbours(x):
    if (x[0] + x[1]) % 2 == 0:
        return (x[0] - 1, x[1]), (x[0] + 1, x[1])
    return (x[0], x[1] - 1), (x[0], x[1] + 1)


def lap(F, x):
    a, b = neighbours(x)
    return F(a) + F(b) - 2 * F(x)


def check_word(w, radius_extra=6):
    Fp, Xi, off = model(w)
    fr = Frame(list(w))
    R = 3 * fr.d + radius_extra
    permA = lambda c, i: Xi(i) <= Xi(c)
    permC = lambda c, i: Xi((c[0] + off[0], c[1] + off[1])) <= Xi((i[0] + off[0], i[1] + off[1]))
    res = {}
    for name, perm in (("A", permA), ("C", permC)):
        bad_m1 = bad_0 = bad_bin = 0
        sample = 0
        for x in range(-R, R + 1):
            for y in range(-R, R + 1):
                c = (x, y)
                l = lap(Fp, c)
                if l not in (-1, 0):
                    bad_bin += 1
                a, b = neighbours(c)
                if l == -1:
                    if not (perm(c, a) and perm(c, b)):
                        bad_m1 += 1
                elif l == 0:
                    if not (perm(c, a) or perm(c, b)):
                        bad_0 += 1
                sample += 1
        res[name] = (bad_m1, bad_0, bad_bin, sample)
    return res


def proper_words(maxlen):
    for L in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=L):
            if any(x != 3 for x in w):
                yield w


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    total = {"A": [0, 0, 0], "C": [0, 0, 0]}
    words = 0
    worst = []
    for w in proper_words(maxlen):
        words += 1
        r = check_word(w)
        for name in ("A", "C"):
            bm1, b0, bb, _ = r[name]
            total[name][0] += bm1
            total[name][1] += b0
            total[name][2] += bb
            if bm1 or b0 or bb:
                worst.append((name, w, bm1, b0, bb))
    print("proper words checked:", words, "max length", maxlen)
    for name in ("A", "C"):
        print(name, "PermitLocal violations (laplacian -1, laplacian 0, non-binary):", total[name])
    for item in worst[:10]:
        print("  violation:", item)
