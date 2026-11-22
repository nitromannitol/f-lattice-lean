"""Task 33: standard and alternate tiles of the Farey recursion, as finite sets of cells (lower-left corners).

Port of FLatticePaper/Tiles/StandardTiles.lean (standard tiles, registers, base words) and of
farey_recursion.tex def:alternate_tiles (eq:alt_decomp, eq:alt_doubled, eq:alt_offsets_w1_odd/even, the omitted pieces
by the type of the last letter, and the base alternate tiles of prop:base_cases).

Fractions are pairs (num, den). Parents are pairs (odd, even). Words are strings over '1','2','3'.
"""
import sys

# ---------- sites, tiles ----------

def add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def sub(u, v):
    return (u[0] - v[0], u[1] - v[1])


def neg(u):
    return (-u[0], -u[1])


def shift(T, v):
    return frozenset(add(x, v) for x in T)


def rot(T):
    # mulI (x, y) = (-y, x)
    return frozenset((-y, x) for (x, y) in T)


def box_filter(xs, ys, pred):
    return frozenset((x, y) for x in xs for y in ys if pred((x, y)))


# ---------- Farey fractions and parents ----------

def rotate(f):
    n, d = f
    if (n + d) % 2 == 1:
        return (d - n, d + n)
    return ((d - n) // 2, (d + n) // 2)


ROOT = ((0, 1), (1, 1))


def combine(P, oc, ec):
    odd, even = P
    return (oc * odd[0] + ec * even[0], oc * odd[1] + ec * even[1])


def current(P, parity):
    return combine(P, 1, 1) if parity == 'odd' else combine(P, 2, 1)


def step(P, digit):
    odd, even = P
    if digit == '1':
        return (current(P, 'odd'), current(P, 'even'))
    if digit == '2':
        return (current(P, 'odd'), even)
    return (odd, current(P, 'even'))


def parents_at(word):
    P = ROOT
    for d in word:
        P = step(P, d)
    return P


def phase(word):
    return word.count('1') % 2


def swapW(word):
    return ''.join({'1': '1', '2': '3', '3': '2'}[d] for d in word)


# texV1Odd p = (2 den, 2 num), texV1Even q = (den, num), texV2 f = (num - den, num + den)
def V1o(p):
    return (2 * p[1], 2 * p[0])


def V1e(q):
    return (q[1], q[0])


def V2(f):
    return (f[0] - f[1], f[0] + f[1])


def tF(f):
    n, d = f
    return (-(n + d), n + 1 - d)


# ---------- standard base tiles (StandardTiles.lean) ----------

def stairF(d):
    def p(x):
        x1, x2 = x
        return ((2 - d <= x1 <= d and 0 <= x2 <= d + 1 and 1 <= x1 + x2 <= d + 2)
                or (x1 == 0 and x2 == 0) or (x1 == 2 and x2 == d + 1))
    return box_filter(range(2 - d, d + 1), range(0, d + 2), p)


def nstairF(d):
    def p(x):
        x1, x2 = x
        return ((0 <= x1 <= d + 1 and 1 <= x2 <= 2 * d - 1 and -1 <= x2 - x1 <= d)
                or (x1 == 0 and x2 == d + 1) or (x1 == d + 1 and x2 == d - 1))
    return box_filter(range(0, d + 2), range(1, 2 * d), p)


def ladderF(d):
    def p(x):
        x1, x2 = x
        a = ((x1 == 0 and x2 == 0) or (x1 == d + 2 and x2 == d + 2)
             or (x1 + x2 == d + 2 and 1 < x2 < d + 1)
             or (2 - d <= x1 <= 2 * d and 0 <= x2 <= d + 2 and 1 <= x1 + x2 <= 2 * d + 3))
        b = (d <= x1 and x2 == 0) or (x1 <= 2 and x2 == d + 2)
        return a and not b
    return box_filter(range(2 - d, 2 * d + 1), range(0, d + 3), p)


def nladderF(d):
    def p(x):
        x1, x2 = x
        a = ((x1 == -1 and x2 == 2 * d + 1) or (x1 == d + 1 and x2 == d - 1)
             or (x2 - x1 == d and 0 < x1 < d)
             or (-1 <= x1 <= d + 1 and 1 <= x2 <= 3 * d - 1 and -1 <= x2 - x1 <= 2 * d + 1))
        b = (x1 == -1 and x2 <= d + 1) or (x1 == d + 1 and 2 * d - 1 <= x2)
        return a and not b
    return box_filter(range(-1, d + 2), range(1, 3 * d), p)


def nstairN(d):
    return shift(nstairF(d), (0, -1))


def nladderN(d):
    return shift(nladderF(d), (0, -1))


# ---------- standard decompositions (oddChildB / evenChildB) ----------

def oddChild(flag, T1, T2, p, q):
    if flag:
        return (shift(T2, V1o(p)) | shift(T2, add(V1o(p), V1e(q))) | shift(T2, V2(p))
                | shift(T2, add(V2(p), V1e(q))) | T1
                | shift(T1, add(add(V1e(q), V1e(q)), V2(q))))
    return (T2 | shift(T2, V1e(q)) | shift(T2, add(V1o(p), V2(p)))
            | shift(T2, add(add(V1o(p), V2(p)), V1e(q)))
            | shift(T1, add(V1e(q), V1e(q))) | shift(T1, V2(q)))


def evenChild(flag, T1, T2, p, q):
    if flag:
        return (shift(T2, V1o(p)) | shift(T2, add(V2(p), V2(p))) | T1 | shift(T1, V2(p))
                | shift(T1, add(V1e(q), V2(q)))
                | shift(T1, add(add(V1e(q), V2(q)), V2(p))))
    return (T2 | shift(T2, add(V1o(p), add(V2(p), V2(p)))) | shift(T1, V1e(q))
            | shift(T1, add(V1e(q), V2(p))) | shift(T1, V2(q)) | shift(T1, add(V2(q), V2(p))))


# ---------- standard registers ----------

ZERO = frozenset({(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)})
ONE = frozenset({(0, 0), (0, 1), (1, 0), (1, 1)})


def is_all(word, digit):
    return len(word) > 0 and all(d == digit for d in word)


def std_children(word, s):
    """s = (par, tOdd, tEven): the standard tiles of the children of `word`."""
    par, tO, tE = s
    if word == '':
        return (nstairN(3), stairF(3))
    if is_all(word, '3'):
        k = len(word)
        return (ladderF(2 * k + 2), stairF(2 * k + 3))
    if is_all(word, '2'):
        k = len(word)
        return (nstairN(2 * k + 3), nladderN(2 * k + 2))
    flag = phase(word) == 1
    return (oddChild(flag, tO, tE, par[0], par[1]), evenChild(flag, tO, tE, par[0], par[1]))


def std_step(pre, s, d):
    par, tO, tE = s
    c1, c2 = std_children(pre, s)
    if d == '1':
        return (step(par, '1'), c1, c2)
    if d == '2':
        return (step(par, '2'), c1, tE)
    return (step(par, '3'), tO, c2)


def std_state(word):
    s = (ROOT, ZERO, ONE)
    pre = ''
    for d in word:
        s = std_step(pre, s, d)
        pre += d
    return s


def std_odd(word):
    return std_children(word, std_state(word))[0]


def std_even(word):
    return std_children(word, std_state(word))[1]


# ---------- normalisation ----------

def lowest(T):
    """c(T): least height, then least abscissa."""
    return min(T, key=lambda p: (p[1], p[0]))


def is_normalised(T):
    return (0, 0) in T and all((0, 0)[1] < p[1] or (p[1] == 0 and 0 <= p[0]) for p in T)


def normalise(T):
    c = lowest(T)
    return shift(T, neg(c))


# ---------- alternate base tiles (prop:base_cases, the alternate rows) ----------

def alt_stair(d):
    # paperStairAltTile d = A u B u C u D (BaseCaseRecurrence.lean)
    def p(x):
        x1, x2 = x
        A = (x1 == 1 - d and -1 <= x2 <= 0) or (x1 == 3 and d <= x2 <= d + 1)
        B = x1 + x2 == 2 and 0 < x2 < d
        C = (1 - d <= x1 <= 0 and x2 == -1) or (4 - d <= x1 <= 3 and x2 == d + 1)
        D = 4 - 2 * d <= x1 <= d and 0 <= x2 <= d and -d + 2 <= x1 + x2 <= d + 2
        return A or B or C or D
    return box_filter(range(4 - 2 * d - 1, d + 4), range(-2, d + 3), p)


def alt_ladder(d):
    # paperLadderAltTile d = (A u B u C) \ D
    def p(x):
        x1, x2 = x
        A = (x1, x2) in ((-1, -1), (d, d + 2))
        B = x1 + x2 == d and 0 < x1 < d - 1
        C = 1 - d <= x1 <= 2 * d - 2 and -1 <= x2 <= d + 2 and -1 <= x1 + x2 <= 2 * d + 1
        D = (d <= x1 and -1 <= x2 <= 0) or (x1 <= -1 and d + 1 <= x2 <= d + 2)
        return (A or B or C) and not D
    return box_filter(range(-d - 3, 2 * d + 3), range(-3, d + 5), p)


def alt_near_stair(d):
    # paperNearStairAltTile d = A u B u C u D (NearOneBaseCases.lean)
    def p(x):
        x1, x2 = x
        A = (-1 <= x1 <= 0 and x2 == 2 * d) or (d <= x1 <= d + 1 and x2 == d - 2)
        B = x2 - x1 == d - 1 and 0 < x1 < d
        C = (x1 == -1 and d + 1 <= x2 <= 2 * d) or (x1 == d + 1 and d - 2 <= x2 <= 2 * d - 3)
        D = 0 <= x1 <= d and 1 <= x2 <= 3 * d - 3 and -1 <= x2 - x1 <= 2 * d - 1
        return A or B or C or D
    return box_filter(range(-2, d + 3), range(-2, 3 * d + 1), p)


def alt_near_ladder(d):
    # paperNearLadderAltTile d = (A u B u C) \ D (NearOneBaseCases.lean)
    def p(x):
        x1, x2 = x
        A = (x1, x2) in ((-2, 2 * d), (d + 1, d - 1))
        B = x2 - x1 == d and 0 < x1 < d - 1
        C = -2 <= x1 <= d + 1 and 1 <= x2 <= 3 * d - 2 and -1 <= x2 - x1 <= 2 * d + 1
        D = (x1 <= -1 and x2 <= d - 1) or (d <= x1 and 2 * d <= x2)
        return (A or B or C) and not D
    return box_filter(range(-3, d + 3), range(-1, 3 * d + 1), p)


# ---------- alternate registers and recursion (def:alternate_tiles) ----------

def alt_pieces(word, s):
    """The alternate tiles (odd child, even child) of `word`, from the state s = (par, tO, tE, aO, aE).

    PROVISIONAL reading of def:alternate_tiles, eq:alt_decomp, eq:alt_doubled, eq:alt_offsets_w1_odd/even and the
    placements of the alternate pieces (types 1, 2, 3 = last letter of `word`; a piece is omitted where the TeX writes -).
    The origin of each alternate tile is the origin of its listed offsets (the TeX's c(T-hat))."""
    par, tO, tE, aO, aE = s
    p1, q1 = par
    flag = phase(word) == 1
    typ = word[-1]
    V1o_p, V2_p, V1e_q, V2_q = V1o(p1), V2(p1), V1e(q1), V2(q1)
    if flag:
        Sp = add(neg(V1e_q), V2_p)
        Sq = add(V1e_q, V2_p)
    else:
        Sp = add(V1e_q, V2_p)
        Sq = add(neg(V1e_q), V2_p)

    def dsP(o):
        return shift(tO, o) | shift(tO, add(o, Sp))

    def dsQ(o):
        return shift(tE, o) | shift(tE, add(o, Sq))

    Z = (0, 0)
    if flag:
        odd = (shift(tE, V1o_p) | shift(tE, sub(add(V2_p, V2_p), V1e_q))
               | dsP(Z) | dsP(add(V1e_q, V2_q)))
        odd_alt = add(add(V2_p, V1o_p), neg(V1e_q)) if typ in '13' else None   # aE placed here
        even = (dsQ(V1o_p) | dsQ(V2_p) | shift(tO, Z) | shift(tO, add(add(V2_p, V2_q), add(V1e_q, V1e_q))))
        if typ == '1':
            even_alt = add(V2_p, V1e_q)
        elif typ == '2':
            even_alt = add(add(V1e_q, V1e_q), V2_q)
        else:
            even_alt = None
    else:
        odd = (shift(tE, Z) | shift(tE, add(V1o_p, add(add(V2_p, V2_p), V1e_q)))
               | dsP(V1e_q) | dsP(V2_q))
        odd_alt = add(V2_p, V1e_q) if typ in '13' else None
        even = (dsQ(Z) | dsQ(add(V1o_p, V2_p)) | shift(tO, V1e_q)
                | shift(tO, sub(add(V2_p, V2_q), V1e_q)))
        if typ == '1':
            even_alt = add(add(V2_p, V1o_p), neg(V1e_q))
        elif typ == '2':
            even_alt = V2_q
        else:
            even_alt = None
    # the alternate pieces: aE (= T-hat(q1)) inside the odd child, aO (= T-hat(p1)) inside the even child
    if odd_alt is not None:
        odd = odd | shift(aE, odd_alt)
    if even_alt is not None:
        even = even | shift(aO, even_alt)
    return odd, even


def alt_base(word):
    """The alternate tiles of the children of a base word (prop:base_cases, the alternate rows).
    PROVISIONAL normalisation: each base alternate tile is translated so that c = 0."""
    if word == '':
        a1, a2 = shift(alt_near_stair(3), (0, -1)), alt_stair(3)
    elif is_all(word, '3'):
        k = len(word)
        a1, a2 = alt_ladder(2 * k + 2), alt_stair(2 * k + 3)
    else:
        k = len(word)
        a1, a2 = shift(alt_near_stair(2 * k + 3), (0, -1)), shift(alt_near_ladder(2 * k + 2), (0, -1))
    if NORMALISE_BASE:
        a1, a2 = normalise(a1), normalise(a2)
    return a1, a2


def alt_children(word, s):
    if word == '' or is_all(word, '2') or is_all(word, '3'):
        return alt_base(word)
    return alt_pieces(word, s)


def alt_step(pre, s, d):
    par, tO, tE, aO, aE = s
    c1, c2 = std_children(pre, (par, tO, tE))
    a1, a2 = alt_children(pre, s)
    if d == '1':
        return (step(par, '1'), c1, c2, a1, a2)
    if d == '2':
        return (step(par, '2'), c1, tE, a1, aE)
    return (step(par, '3'), tO, c2, aO, a2)


def alt_state(word):
    s = (ROOT, ZERO, ONE, ZERO, ONE)
    pre = ''
    for d in word:
        s = alt_step(pre, s, d)
        pre += d
    return s


def alt_odd(word):
    return alt_children(word, alt_state(word))[0]


def alt_even(word):
    return alt_children(word, alt_state(word))[1]


NORMALISE_BASE = True


def main(argv):
    print("module loaded")


if __name__ == "__main__":
    main(sys.argv[1:])
