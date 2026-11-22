"""Task 53 (part 2): numerical check of hbaseThree, the reciprocal base identity.

For the word 3^k (den d = 2k+3) the standard field is F = B1(d) (proto2.py), the plane alternate is the midpoint
H(x) = ceil((F(x) + F(x + sigma)) / 2) with sigma = 2 eps (D, N) of the odd parent of the word (Frame), and the explicit base
alternate of Construction/AlternateStaircaseExtension.lean is A(x) = F(x - (1, 0)) + marker(x), marker(x) = 1 iff
staircaseLevel(x) = x1 - d x2 is congruent mod T = d^2 + 2d - 1 to 2 - (d+1) row for some row in [1, d-1].
The identity holds up to one constant iff H - A is constant on the window.
"""
import sys
from pathlib import Path

PROTO = Path.home() / "rwc-wc" / "fl" / "proto" / "proto2.py"


def load():
    src = PROTO.read_text()
    ns = {}
    exec(compile(src[: src.index("for L_ in range(1,4):")], "proto2_defs", "exec"), ns)
    return ns


def marker(d, x):
    T = d * d + 2 * d - 1
    level = x[0] - d * x[1]
    return 1 if any(level % T == (2 - (d + 1) * row) % T for row in range(1, d)) else 0


def main():
    ns = load()
    standard, Frame = ns["standard"], ns["Frame"]
    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for k in range(0, k_max + 1):
        w = tuple([3] * k)
        F = standard(w)[0]
        fr = Frame(list(w))
        d = fr.d
        assert d == 2 * k + 3, (k, d)
        sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
        H = lambda x: -((-(F(x) + F((x[0] + sig[0], x[1] + sig[1])))) // 2)  # ceil((F+G)/2)
        A = lambda x: F((x[0] - 1, x[1])) + marker(d, x)
        diffs = set()
        cnt = 0
        for x1 in range(-3 * d, 3 * d + 1):
            for x2 in range(-3 * d, 3 * d + 1):
                x = (x1, x2)
                diffs.add(H(x) - A(x))
                cnt += 1
        print(f"k={k} d={d} sigma={sig} window={cnt} distinct values of H-A: {sorted(diffs)[:10]}"
              f"{' ...' if len(diffs) > 10 else ''} (#{len(diffs)})")


if __name__ == "__main__":
    main()
