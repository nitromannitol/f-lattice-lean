"""I2 case facts (task 49): for z in the harmonic region, u = z - W V:
(a) -eps*u_y in [0, L] (and u_y determined); (b) k = t_p(u) in (W=0: k <= 2N; W=1: k > -N);
(c) m = s_p(u): G(u) = F(Z u) is 0 for m <= 2r-1, -1 for m = 2r, >= -1 for m = 2r+1 (G = f - h0);
(d) R(u + k' V_p) = R(u) - k' eps."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import upper_attainment_check as uac  # noqa: E402

standard = uac.standard


def main(maxlen):
    st = dict(pts=0, a_ok=0, b_ok=0, c0_ok=0, c1_ok=0, c2_ok=0, d_ok=0, dtot=0)
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
        Vp = (-b, r)
        Vq = (nq - dq, nq + dq)
        V = (2 * Vp[0] + Vq[0], 2 * Vp[1] + Vq[1])
        h0 = uac.harmonic

        def G(x):
            return F((-x[1], x[0] - 1))

        def f(x):
            return G(x) + h0(x)

        def sp(x):
            return r * x[0] + b * x[1]

        def tp(x):
            return N * x[0] - D * x[1]

        def R(u):
            return f((u[0] - Uq[0], u[1] - Uq[1])) - h0(u)

        for a in range(-2 * L - 4, 2 * L + 5):
            for c in range(-2 * L - 4, 2 * L + 5):
                z = (a, c)
                if not uac.in_closed_polygon(fw, z):
                    continue
                s = (d + n) * z[0] + (d - n) * z[1]
                if s > 2 * L - 1:
                    continue
                st["pts"] += 1
                u = (z[0] - W * V[0], z[1] - W * V[1])
                m = sp(u)
                k = tp(u)
                # (a)
                if 0 <= -eps * u[1] <= L:
                    st["a_ok"] += 1
                else:
                    bad.append(("a", word, z, u))
                # (b)
                okb = (k <= 2 * N) if W == 0 else (k > -N)
                if okb:
                    st["b_ok"] += 1
                else:
                    bad.append(("b", word, z, k))
                # (c)
                if m <= 2 * r - 1:
                    if G(u) == 0:
                        st["c0_ok"] += 1
                    else:
                        bad.append(("c0", word, z, m, G(u)))
                elif m == 2 * r:
                    if G(u) == -1:
                        st["c1_ok"] += 1
                    else:
                        bad.append(("c1", word, z, m, G(u)))
                else:
                    if G(u) >= -1:
                        st["c2_ok"] += 1
                    else:
                        bad.append(("c2", word, z, m, G(u)))
                # (d): shift by k' V_p
                for kp in (1, -1):
                    st["dtot"] += 1
                    up = (u[0] + kp * Vp[0], u[1] + kp * Vp[1])
                    if R(up) == R(u) - kp * eps:
                        st["d_ok"] += 1
                    else:
                        bad.append(("d", word, z, kp, R(up), R(u)))
    print(st)
    print("failures", len(bad))
    for item in bad[:8]:
        print(item)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
