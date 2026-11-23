"""Exact check of the Lean predicate UpperAttainment (Construction/NominalAgreement.lean), word by word (task 48, step 1).

UpperAttainment word := ∀ z ∈ closedPolygon(frameAt word),
    2 (den + num) - 1 < sGrade z  →  sheetC Fp z ≤ sheetA Fp z,
with Fp = quarterTurnField (standardField (conjWord word)), all definitions transcribed from the Lean files:
  parentsAt word = (odd, even) from the proto parents (seventh_jet.parents_of); child = 2 odd + even (Parents.current .even);
  eps = odd.det even = N dq - nq D (Fraction.det first second = first.num second.den - second.num first.den);
  closedPolygon (Sheets.lean): EvenSite z = ((z1 + z2) % 2 = 0); even case 2 - T ≤ t ≤ den + num - 2, 0 ≤ s ≤ T + 2 num;
    odd case num - T ≤ t ≤ den, 2 - den + num ≤ s ≤ T + den + num - 2; T = child.periodDenominator = den² + 2 den num - num²;
  tGrade z = num z1 - den z2 (child), sGrade z = (den + num) z1 + (den - num) z2 (ChildFrame.sGrade);
  sheetShift = (1 - W) (dq, nq), W = (1 + eps) / 2; sheetOffset = (nq - dq, dq + nq) + eps (dq, nq);
  siblingSlope x = nq x1 - dq x2; sheetConstant = (T_q - dq - nq) / 2 + 2 W with T_q = dq² + 2 dq nq - nq²;
  sheetA Fp z = Fp (z - shift); sheetC Fp z = Fp (z - shift - offset) + siblingSlope (z - shift) + sheetConstant;
  quarterTurnField F x = F (Z x) + harmonicGrid x, Z(x) = (-x2, x1 - 1); harmonicGrid x = (x1² + 2 x1 x2 - x2² - 2 x2 - (x1+x2)%2) / 4;
  conjWord word = (oddBirthPrefix word).map swap, oddBirthPrefix word = ((word.reverse.dropWhile (= three)).drop 1).reverse.
Int division is Lean's `/` (Euclidean; the divisors are positive, so it is floor division, as Python's //).
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ordinary_tile_check as otc  # noqa: E402
from seventh_jet import parents_of  # noqa: E402

NS = otc.load_proto()
standard = NS["standard"]


def swap(d):
    return {1: 1, 2: 3, 3: 2}[d]


def oddBirthPrefix(word):
    r = list(reversed(word))
    i = 0
    while i < len(r) and r[i] == 3:
        i += 1
    r = r[i:]
    r = r[1:]
    return list(reversed(r))


def conjWord(word):
    return [swap(d) for d in oddBirthPrefix(word)]


def harmonic(x):
    x1, x2 = x
    return (x1 * x1 + 2 * x1 * x2 - x2 * x2 - 2 * x2 - (x1 + x2) % 2) // 4


def make_frame(word):
    (N, D), (nq, dq) = parents_of(tuple(word))
    n = 2 * N + nq  # child numerator (Parents.current .even = combine 2 1)
    d = 2 * D + dq  # child denominator
    eps = N * dq - nq * D  # odd.det even
    T = d * d + 2 * d * n - n * n  # child.periodDenominator
    W = (1 + eps) // 2
    shift = ((1 - W) * dq, (1 - W) * nq)
    offset = (nq - dq + eps * dq, dq + nq + eps * nq)
    Tq = dq * dq + 2 * dq * nq - nq * nq
    sconst = (Tq - dq - nq) // 2 + 2 * W
    F = standard(tuple(conjWord(word)))[0]

    def Fp(x):
        return F((-x[1], x[0] - 1)) + harmonic(x)

    def sheetA(z):
        return Fp((z[0] - shift[0], z[1] - shift[1]))

    def sheetC(z):
        y = (z[0] - shift[0], z[1] - shift[1])
        return Fp((y[0] - offset[0], y[1] - offset[1])) + (nq * y[0] - dq * y[1]) + sconst

    return dict(n=n, d=d, T=T, eps=eps, sheetA=sheetA, sheetC=sheetC, nq=nq, dq=dq, N=N, D=D)


def t_grade(fr, z):
    return fr["n"] * z[0] - fr["d"] * z[1]


def s_grade(fr, z):
    return (fr["d"] + fr["n"]) * z[0] + (fr["d"] - fr["n"]) * z[1]


def in_closed_polygon(fr, z):
    n, d, T = fr["n"], fr["d"], fr["T"]
    t, s = t_grade(fr, z), s_grade(fr, z)
    if (z[0] + z[1]) % 2 == 0:
        return (2 - T <= t <= d + n - 2) and (0 <= s <= T + 2 * n)
    return (n - T <= t <= d) and (2 - d + n <= s <= T + d + n - 2)


def polygon_box(fr):
    """A box containing the closed polygon: the inverse grade map at the corners of the (t, s) rectangle."""
    n, d, T = fr["n"], fr["d"], fr["T"]
    L = d + n
    ts = [2 - T, n - T, d + n - 2, d]
    ss = [0, 2 - d + n, T + 2 * n, T + d + n - 2]
    zs0, zs1 = [], []
    for t in ts:
        for s in ss:
            zs0.append(((d - n) * t + d * s) / T)
            zs1.append((-L * t + n * s) / T)
    import math
    return (math.floor(min(zs0)) - 1, math.ceil(max(zs0)) + 1, math.floor(min(zs1)) - 1, math.ceil(max(zs1)) + 1)


def check_word(word):
    """Return (number of polygon points, number of upper points, failing points) for the predicate on this word."""
    fr = make_frame(word)
    x0, x1, y0, y1 = polygon_box(fr)
    bound = 2 * (fr["d"] + fr["n"]) - 1
    npoly = nupper = 0
    fails = []
    for z0 in range(x0, x1 + 1):
        for z1 in range(y0, y1 + 1):
            z = (z0, z1)
            if not in_closed_polygon(fr, z):
                continue
            npoly += 1
            if bound < s_grade(fr, z):
                nupper += 1
                if not (fr["sheetC"](z) <= fr["sheetA"](z)):
                    fails.append((z, fr["sheetC"](z), fr["sheetA"](z)))
    return npoly, nupper, fails, fr


def words_up_to(k):
    out = []
    for L in range(0, k + 1):
        for w in itertools.product((1, 2, 3), repeat=L):
            out.append(tuple(w))
    return out


if __name__ == "__main__":
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    failing_words = []
    for w in words_up_to(k):
        npoly, nupper, fails, fr = check_word(w)
        status = "holds" if not fails else f"FAILS at {len(fails)} points"
        print(w, "polygon points", npoly, "upper points", nupper, "UpperAttainment:", status, flush=True)
        if fails:
            failing_words.append((w, fails[:3]))
    print("words checked:", len(words_up_to(k)), "failing words:", len(failing_words))
    for w, f in failing_words[:5]:
        print("  first failing point for", w, ":", f)
