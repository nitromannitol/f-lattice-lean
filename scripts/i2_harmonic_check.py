"""I2 harmonic region (task 49, fix Q4-strips): for proper words, on E ∩ {s <= 2L - 1} (L = d + n) check
(i) the other sheet minus h0 at z is >= 0 (A(z) for eps = -1, C(z) for eps = +1);
(ii) R(u) = f(u - U_q) - h0(u) with u = z - W V (V = 2 V_p + V_q) equals that difference (identity (4));
(iii) the range 1 - r <= m <= 2r + 1 for m = s_p(u), m = b u... (s_p(u) = r u1 + b u2)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import upper_attainment_check as uac  # noqa: E402

standard = uac.standard


def main(maxlen):
    stats = dict(pts=0, other_ok=0, ident_ok=0, m_ok=0, R_ok=0)
    bad = []
    for word in uac.words_up_to(maxlen):
        if not any(x != 3 for x in word):
            continue
        fw = uac.make_frame(word)
        u_conj = uac.conjWord(word)
        F = standard(tuple(u_conj))[0]
        N, D, eps = fw["N"], fw["D"], fw["eps"]
        nq, dq, n, d = fw["nq"], fw["dq"], fw["n"], fw["d"]
        r, b = D + N, D - N
        L = d + n
        W = (1 + eps) // 2
        Uq = (dq, nq)
        Up = (2 * D, 2 * N)
        Vp = (-b, r)
        Vq = (nq - dq, nq + dq)
        V = (2 * Vp[0] + Vq[0], 2 * Vp[1] + Vq[1])
        h0 = uac.harmonic

        def f(x):
            return F((-x[1], x[0] - 1)) + h0(x)

        def sp(x):
            return r * x[0] + b * x[1]

        def tp(x):
            return N * x[0] - D * x[1]

        for a in range(-2 * L - 4, 2 * L + 5):
            for c in range(-2 * L - 4, 2 * L + 5):
                z = (a, c)
                if not uac.in_closed_polygon(fw, z) or d * a + n * c > 0 and False:
                    continue
                s = (d + n) * z[0] + (d - n) * z[1]
                if s > 2 * L - 1:
                    continue
                stats["pts"] += 1
                if eps == -1:
                    other = fw["sheetA"](z)
                else:
                    other = fw["sheetC"](z)
                if other - h0(z) >= 0:
                    stats["other_ok"] += 1
                else:
                    bad.append(("other", word, z, other - h0(z)))
                u = (z[0] - W * V[0], z[1] - W * V[1])
                R = f((u[0] - Uq[0], u[1] - Uq[1])) - h0(u)
                if R == other - h0(z):
                    stats["ident_ok"] += 1
                else:
                    bad.append(("ident", word, z, R, other - h0(z)))
                m = sp(u)
                if 1 - r <= m <= 2 * r + 1:
                    stats["m_ok"] += 1
                else:
                    bad.append(("m", word, z, m))
                if R >= 0:
                    stats["R_ok"] += 1
                else:
                    bad.append(("R", word, z, R))
    print(stats)
    print("failures", len(bad))
    for item in bad[:8]:
        print(item)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
