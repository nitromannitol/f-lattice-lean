"""Task 53 (part 2): numerical check of hbaseTwoId, the rotated ladder base identity.

Word 2^(k+1): the standard field F is the proto standard field (proto2.py); the plane alternate is the midpoint
H(x) = ceil((F(x) + F(x + sigma)) / 2), sigma = 2 eps (D, N) of the odd parent of the word (Frame).

The explicit side (Lean): rotateLadderAltField d S (x) = S(2d-2-x2, x1+1) + centeredQuarterTurnCorrection(x) + x1 + 1, where
S is the periodic extension of the raw ladderOddAlt tile (ladderOddAltValue on the sites of mem_ladderOddAlt_raw_iff) with
generator identities (kernel (2d, 2), transverse (1-d, 1+d), periodDenominator T = d^2+2d-1, constants (-1, ladderOddAltConstantV)).
S(x) = value(r) + periodIncrement(r, i, j) for any x = r + i*kernel + j*transverse with r in the raw tile.
The identity holds up to one constant iff H - E is constant on the window.
"""
import sys
from pathlib import Path

PROTO = Path.home() / "rwc-wc" / "fl" / "proto" / "proto2.py"


def load():
    src = PROTO.read_text()
    ns = {}
    exec(compile(src[: src.index("for L_ in range(1,4):")], "proto2_defs", "exec"), ns)
    return ns


def choose2(n):
    return n * (n - 1) // 2


def in_raw(d, x):
    x1, x2 = x
    if not (1 - d <= x1 <= 2 * d - 2 and -1 <= x2 <= d + 2):
        return False
    corner = (x1 == -1 and x2 == -1) or (x1 == d and x2 == d + 2)
    if corner:
        return True
    band = -1 <= x1 + x2 <= 2 * d + 1
    excl = (-1 <= x2 <= 0 and d <= x1) or (d + 1 <= x2 <= d + 2 and x1 <= -1)
    return band and not excl


def value(d, x):
    x1, x2 = x
    corner = (x1 == -1 and x2 == -1) or (x1 == d and x2 == d + 2)
    diagonal = x1 + x2 == d and 0 < x1 < d - 1
    return (-(x2 * (x2 + 1) // 2) + min(x1, 0) + max(x1 + x2 - d, 0) + min(d - x1 - 1, 0)
            + (1 if (corner or diagonal) else 0))


def make_S(d, search=10):
    kernel = (2 * d, 2)            # mu = 2 for d even (num + den odd)
    transverse = (1 - d, 1 + d)
    T = d * d + 2 * d - 1
    cU = -1
    cV = -choose2(d + 1) - 2 * d + 1
    def tg(x):
        return d * x[1] - x[0]     # transverseGrade of 1/d

    def S(x):
        vals = []
        for i in range(-search, search + 1):
            for j in range(-search, search + 1):
                r = (x[0] - i * kernel[0] - j * transverse[0], x[1] - i * kernel[1] - j * transverse[1])
                if in_raw(d, r):
                    inc = i * cU + j * (cV - tg(r)) - T * choose2(j)
                    vals.append(value(d, r) + inc)
        assert vals, ("no representative", x)
        assert len(set(vals)) == 1, ("inconsistent", x, sorted(set(vals))[:4])
        return vals[0]

    return S


def cqtc(x):
    x1, x2 = x
    return choose2(x1) - ((x1 - x2 - 1) ** 2) // 4


def main():
    ns = load()
    standard, Frame = ns["standard"], ns["Frame"]
    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    for k in range(0, k_max + 1):
        w = tuple([2] * (k + 1))
        d = 2 * k + 4
        F = standard(w)[0]
        fr = Frame(list(w))
        assert fr.n == 2 * k + 3 and fr.d == 2 * k + 5, (k, fr.n, fr.d)
        sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
        H = lambda x: -((-(F(x) + F((x[0] + sig[0], x[1] + sig[1])))) // 2)
        S = make_S(d)
        E = lambda x: S((2 * d - 2 - x[1], x[0] + 1)) + cqtc(x) + x[0] + 1
        diffs = set()
        cnt = 0
        R = 3 * d
        for x1 in range(-R, R + 1, 2):
            for x2 in range(-R, R + 1, 2):
                x = (x1, x2)
                diffs.add(H(x) - E(x))
                cnt += 1
        print(f"k={k} d={d} sigma={sig} window={cnt} distinct H-E: {sorted(diffs)[:10]}"
              f"{' ...' if len(diffs) > 10 else ''} (#{len(diffs)})")


if __name__ == "__main__":
    main()
