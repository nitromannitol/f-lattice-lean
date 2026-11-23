"""Task 67 numerics: the bare common-primary-chart claim of SHORT_SLIP_COMMON_CHART (false as stated).

For the even/odd E s-windows I_0 = [0, T+2n] and I_1 = [2-d+n, T+d+n-2] (T = d^2+2dn-n^2, L = d+n), and all even s, s' with |s - s'| <= L,
the claim asks for a common primary index k with s - kT in the window of s and s' - kT in the window of s'. The bare claim fails:
(n, d) = (1, 5), s = -2, s' = 4 (both even, window 0): the only k for s is -1 and the only k for s' is 0.
The note's version uses the t-support of the endpoints and the edge structure (w = z +- eps Up etc.), which this check does not model.
"""
from math import gcd


def failures(dmax=14):
    bad, tot, examples = 0, 0, []
    for d in range(3, dmax + 1):
        for n in range(1, d - 1):
            if gcd(n, d) != 1 or (d + n) % 2:
                continue
            L = d + n
            T = d * d + 2 * d * n - n * n
            win = {0: (0, T + 2 * n), 1: (2 - d + n, T + d + n - 2)}

            def ks(s, p):
                lo, hi = win[p]
                return {k for k in range(-4, 5) if lo <= s - k * T <= hi}

            for s in range(-2 * T, 2 * T, 2):
                for sp in range(s - L, s + L + 1, 2):
                    for p in (0, 1):
                        for q in (0, 1):
                            A, B = ks(s, p), ks(sp, q)
                            if not A or not B:
                                continue
                            tot += 1
                            if not (A & B):
                                bad += 1
                                if len(examples) < 5:
                                    examples.append((n, d, s, sp, p, q, sorted(A), sorted(B)))
    return tot, bad, examples


if __name__ == '__main__':
    tot, bad, ex = failures()
    print('pairs tested', tot, 'without common k', bad)
    for e in ex:
        print(e)
