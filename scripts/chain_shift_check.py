"""Task 72 (a) numeric checks.

1. Identities used by the chain-pair statement (STRONG_PRICE_AND_ALTERNATE_STEP section 4):
   D_eta(z) = F(z) - F(z + eta*sigma), chain potential Phi_eta(z) = D_eta(z) + P(z + eta*sigma),
   P(z) = F(z) - F(z - v) - eps*(a.z); the identities D_eta(z) = -D_{-eta}(z + eta*sigma) and
   Phi_eta(z) = F(z) - F(z + eta*sigma - v) - eps*(a.(z + eta*sigma)) hold for random integer fields.
2. The shortShift sigma = eps*(2D, 2N) (parent odd N/D) lies in the child modified deck span
   {i*K + j*T}, K = (d, n), T = (n - d, n + d), for Farey children n/d = (2N+nq)/(2D+dq)?
   Count how often it does not (the chain shift is not a deck translation in general).
"""
import random
from fractions import Fraction
from math import gcd

random.seed(72)

def check_identities(trials=2000):
    for _ in range(trials):
        N, D = random.randint(-9, 9), random.randint(1, 9)
        nq, dq = random.randint(-9, 9), random.randint(1, 9)
        eps = random.choice([1, -1])
        # generic field values on a window
        table = {}
        def F(z):
            if z not in table:
                table[z] = random.randint(-30, 30)
            return table[z]
        a = (N, -D)
        v = (N - D, N + D)            # V_p
        sigma = (2 * eps * D, 2 * eps * N)   # eps * Up with Up = 2(D, N)
        def P(z):
            return F(z) - F((z[0] - v[0], z[1] - v[1])) - eps * (a[0] * z[0] + a[1] * z[1])
        def Dd(eta, z):
            return F(z) - F((z[0] + eta * sigma[0], z[1] + eta * sigma[1]))
        for eta in (1, -1):
            for _ in range(5):
                z = (random.randint(-20, 20), random.randint(-20, 20))
                zs = (z[0] + eta * sigma[0], z[1] + eta * sigma[1])
                phi = Dd(eta, z) + P(zs)
                assert Dd(eta, z) == -Dd(-eta, zs), "D identity"
                closed = F(z) - F((zs[0] - v[0], zs[1] - v[1])) - eps * (a[0] * zs[0] + a[1] * zs[1])
                assert phi == closed, "chain identity"
    return trials

def in_child_span(d, n, sx, sy):
    """Is (sx, sy) = i*(d, n) + j*(n - d, n + d) for integers i, j?"""
    K = (d, n)
    T = (n - d, n + d)
    det = K[0] * T[1] - K[1] * T[0]          # = d^2 + 2dn - n^2
    i_num = sx * T[1] - sy * T[0]
    j_num = K[0] * sy - K[1] * sx
    return i_num % det == 0 and j_num % det == 0

def enumerate_children(bound=12):
    total = 0
    outside = []
    for D in range(1, bound + 1):
        for N in range(1, bound + 1):
            if gcd(N, D) != 1 or (N + D) % 2 == 0:      # odd parent, reduced
                continue
            for dq in range(1, bound + 1):
                for nq in range(0, bound + 1):
                    if gcd(nq, dq) != 1 or (nq + dq) % 2 != 0:   # even sibling, reduced
                        continue
                    eps = N * dq - D * nq
                    # child n/d = (2N+nq)/(2D+dq)
                    if abs(eps) != 1:
                        continue
                    n, d = 2 * N + nq, 2 * D + dq
                    if (n + d) % 2 != 0 or d <= 0:
                        continue
                    # the child's own eps is N*d - D*n (= eps)
                    sig = (2 * eps * D, 2 * eps * N)
                    total += 1
                    if not in_child_span(d, n, sig[0], sig[1]):
                        outside.append((N, D, nq, dq, n, d, eps, sig))
    return total, outside

if __name__ == "__main__":
    print("identity trials passed:", check_identities())
    total, outside = enumerate_children()
    print("Farey children checked:", total)
    print("children whose shortShift is NOT in the modified deck span:", len(outside))
    for row in outside[:8]:
        N, D, nq, dq, n, d, eps, sig = row
        print(f"  odd {N}/{D}, even {nq}/{dq}, child {n}/{d}, eps={eps}, sigma={sig}")
