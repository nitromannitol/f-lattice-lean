"""Numerical check of the I1 zone argument (task 49, step (d)) for proper words of length <= 3.
Notation: u = conjWord(word); F = standard field of u; G(x) = F(Z x), Z x = (-x2, x1 - 1); h0 = harmonic; f = h0 + G.
w = z - W U, q = w - V_q.  Checks: (1) C(z) = h0(w) + G(q); (2) t_p(w) in [-D, r]; (3) if t_p(w) != -D then
f(w) = 0 and C = G(q) - G(w) >= 0; (4) if t_p(w) = -D: w = (kD, kN+1), k odd gives f(w) = 0; k = 2l gives C = -1 - 2 eps l."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import upper_attainment_check as uac  # noqa: E402

standard = uac.standard


def main(maxlen):
    tot = dict(zone=0, c_id=0, tp_range=0, f0=0, c_nonneg=0, exc=0, exc_odd_f0=0, exc_even_formula=0)
    bad = []
    for word in uac.words_up_to(maxlen):
        if not any(x != 3 for x in word):
            continue
        fw = uac.make_frame(word)
        u = uac.conjWord(word)
        F = standard(tuple(u))[0]
        N, D, eps = fw["N"], fw["D"], fw["eps"]
        nq, dq = fw["nq"], fw["dq"]
        n, d = fw["n"], fw["d"]
        r, b = D + N, D - N
        W = (1 + eps) // 2
        U = (2 * D + dq, 2 * N + nq)
        Vq = (nq - dq, nq + dq)
        h0 = uac.harmonic

        def G(x):
            return F((-x[1], x[0] - 1))

        def f(x):
            return G(x) + h0(x)

        def tp(x):
            return N * x[0] - D * x[1]

        L = 2 * (d + n) + 4
        for a in range(-L, L + 1):
            for c in range(-L, L + 1):
                z = (a, c)
                if not uac.in_closed_polygon(fw, z) or n * a - d * c < 1 - d:
                    continue
                tot["zone"] += 1
                w = (z[0] - W * U[0], z[1] - W * U[1])
                q = (w[0] - Vq[0], w[1] - Vq[1])
                C = fw["sheetC"](z)
                # (1)
                if C == h0(w) + G(q):
                    tot["c_id"] += 1
                else:
                    bad.append(("identity", word, z))
                # (2)
                if -D <= tp(w) <= r:
                    tot["tp_range"] += 1
                else:
                    bad.append(("tp range", word, z, tp(w)))
                if tp(w) != -D:
                    if f(w) == 0:
                        tot["f0"] += 1
                    else:
                        bad.append(("f0", word, z))
                    if G(q) - G(w) >= 0 and C == G(q) - G(w):
                        tot["c_nonneg"] += 1
                    else:
                        bad.append(("c-nonneg", word, z, C, G(q) - G(w)))
                else:
                    tot["exc"] += 1
                    # w = (kD, kN+1)
                    k = w[0] // D if D else None
                    ok = (w[0] == k * D and w[1] == k * N + 1)
                    if not ok:
                        bad.append(("exc form", word, z, w))
                        continue
                    if k % 2 == 1:
                        if f(w) == 0:
                            tot["exc_odd_f0"] += 1
                        else:
                            bad.append(("exc odd f", word, z, w))
                    else:
                        l = k // 2
                        if C == -1 - 2 * eps * l:
                            tot["exc_even_formula"] += 1
                        else:
                            bad.append(("exc even", word, z, C, l, eps))
                        if C < 1:
                            bad.append(("exc even value<1", word, z, C))
    print(tot)
    print("failures", len(bad))
    for item in bad[:8]:
        print(item)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
