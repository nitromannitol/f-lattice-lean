"""Per-word check (task 49, I1 step (c)): closed form of delta - eps*sigma = m*kappa, and the zone window of
j = t_u(Z w) against r: W = 0 should give j <= r, W = 1 should give j >= r."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import upper_attainment_check as uac  # noqa: E402


def main(maxlen):
    rows = []
    for word in uac.words_up_to(maxlen):
        if not any(x != 3 for x in word):
            continue
        fw = uac.make_frame(word)
        u = uac.conjWord(word)
        fu = uac.make_frame(u)
        N, D, eps_w = fw["N"], fw["D"], fw["eps"]
        nq, dq = fw["nq"], fw["dq"]
        b, r = fu["n"], fu["d"]
        Nu, Du, eps_u = fu["N"], fu["D"], fu["eps"]
        sig = (2 * eps_u * Du, 2 * eps_u * Nu)
        delta = (nq + dq, dq - nq)
        s = eps_w
        diff = (delta[0] - s * sig[0], delta[1] - s * sig[1])
        m = diff[0] // r if r else None
        ok_m = (m is not None and diff[0] % r == 0 and diff[1] == m * b)
        W = (1 + eps_w) // 2
        U = (2 * D + dq, 2 * N + nq)
        bad_w0 = bad_w1 = 0
        cnt = 0
        L = 2 * (fw["d"] + fw["n"]) + 4
        for a in range(-L, L + 1):
            for c in range(-L, L + 1):
                z = (a, c)
                if not uac.in_closed_polygon(fw, z) or fw["n"] * a - fw["d"] * c < 1 - fw["d"]:
                    continue
                cnt += 1
                w = (z[0] - W * U[0], z[1] - W * U[1])
                j = r * 0 + (b * (-w[1] + 0) * 0)  # placeholder
                Zw = (-w[1], w[0] - 1)
                j = b * Zw[0] - r * Zw[1]          # t_u(Z w)
                if W == 0 and j > r:
                    bad_w0 += 1
                if W == 1 and j < r:
                    bad_w1 += 1
        rows.append((word, N, D, nq, dq, eps_w, Nu, Du, eps_u, b, r, m, ok_m, bad_w0, bad_w1, cnt))
    for row in rows:
        print("word", row[0], "N,D", row[1:3], "nq,dq", row[3:5], "eps_w", row[5], "N_u,D_u", row[6:8],
              "eps_u", row[8], "b,r", row[9:11], "m", row[11], "ok_m", row[12], "W0 j>r", row[13], "W1 j<r", row[14],
              "zone", row[15], flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2)
