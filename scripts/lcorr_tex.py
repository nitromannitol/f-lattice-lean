"""Task 35: the L-corrections of def:odd_l_correction / def:even_l_correction (farey_recursion.tex 3491-3594) as cell sets,
compared with the constructor's correction outputs (checks/LCorrectionsNative.lean, log lines P and C).

Conventions (all tiles are normalised: lowest cell at the origin, as in native_compare.normalised):
  T(p2), T(q2), T-hat(q2) (odd case) or T-hat(p2) (even case) are the retained registers of the saved word u, which are the
  standard and alternate tiles of the parent pair (p2, q2) = parents_at(u) (the constructor's savedTwo/savedThree registers).
  v_{p,1} = V1o(p) = (2 den, 2 num) for the odd parent, v_{q,1} = V1e(q) = (den, num) for the even parent, v_{.,2} = V2(.).
  W1 = number of 1s in w = phase(u); "+" is the flip flag false, "-" is flip true (checked by the outputs, see below);
  z = 0 (elongated) when the constructor's elongated flag is true.

Two readings of the placement of the bridge and the heads (the TeX text states both c(T(p2)) = c(T(q2)) + K1 k and
(T(p2) + K2), which differ by K1 k):
  'c'   : bridge at k K1 + K2, heads at k K1 + K2 + K3 + i K4 (i = 1 .. 2(k+1)-z)   [c-relations of eq:l_correction_*]
  'lit' : bridge at K2, heads at K3 + i K4                                         [the union formulas read literally]
Usage: python3 lcorr_tex.py LOG
"""
import sys

import alt_tiles as at
import native_compare as nc


def V1o(f):
    return at.V1o(f)


def V1e(f):
    return at.V1e(f)


def V2(f):
    return at.V2(f)


def add(*vs):
    x = sum(v[0] for v in vs)
    y = sum(v[1] for v in vs)
    return (x, y)


def mul(k, v):
    return (k * v[0], k * v[1])


def neg(v):
    return (-v[0], -v[1])


def sub(u, v):
    return (u[0] - v[0], u[1] - v[1])


def shift(T, v):
    return frozenset((x + v[0], y + v[1]) for (x, y) in T)


def union(*Ts):
    out = frozenset()
    for T in Ts:
        out = out | T
    return out


# ---------- parsing the constructor extraction ----------

def parse_lcorr(path):
    P, C = {}, {}
    with open(path) as fh:
        for line in fh:
            line = line.rstrip('\n')
            parts = line.split(' ')
            if parts[0] == 'P':
                u, name = parts[1], parts[2]
                cells = parts[3] if len(parts) > 3 else ''
                P.setdefault(u, {})[name] = cells_of(cells)
            elif parts[0] == 'C':
                parity, x, side, length = parts[1], parts[2], parts[3], parts[4]
                cells = parts[5] if len(parts) > 5 else ''
                C[(parity, x, side, length)] = cells_of(cells)
            elif parts[0] == 'E':
                C[(parts[1], parts[2], parts[3], parts[4])] = None
    return P, C


def cells_of(s):
    if not s:
        return frozenset()
    pts = set()
    for c in s.split(';'):
        x, y = c.split(',')
        pts.add((int(x), int(y)))
    return frozenset(pts)


# ---------- the TeX definitions ----------

def odd_case(u, flip):
    W1 = at.phase(u) == 1
    if W1 and not flip:
        return '10'
    if W1 and flip:
        return '11'
    if not W1 and not flip:
        return '00'
    return '01'


def odd_table(case, p, q):
    """[K1,K2,K3,K4] of eq:l_correction_odd (lines 3513-3530) with p = p2, q = q2."""
    vp1, vq1, vp2, vq2 = V1o(p), V1e(q), V2(p), V2(q)
    if case == '10':
        K12 = (vq2, add(vq2, sub(vq1, vp1)))
        K34 = (add(neg(vq2), vp2, sub(vp1, vq1)), neg(vq1))
    elif case == '11':
        K12 = (vq2, neg(vp2))
        K34 = (sub(vp1, vq1), vq1)
    elif case == '00':
        K12 = (vq2, vq2)
        K34 = (neg(add(vq2, vp2)), vq1)
    else:
        K12 = (neg(vq2), add(neg(vp2), neg(sub(vp1, vq1))))
        K34 = ((0, 0), neg(vq1))
    return K12[0], K12[1], K34[0], K34[1]


def odd_L(u, x, flip, elong, Tp, Tq, Th, variant='c'):
    """The odd L-correction for the word x = u 2^k (k = |x| - |u|): stems T(q2), bridge T(p2), heads T-hat(q2)."""
    p, q = at.parents_at(u)
    k = len(x) - len(u)
    K1, K2, K3, K4 = odd_table(odd_case(u, flip), p, q)
    z = 0 if elong else 1
    stems = [shift(Tq, mul(j, K1)) for j in range(k + 1)]
    if variant == 'c':
        base = add(mul(k, K1), K2)
        bridge = shift(Tp, base)
        heads = [shift(Th, add(base, K3, mul(i, K4))) for i in range(1, 2 * (k + 1) - z + 1)]
    else:
        bridge = shift(Tp, K2)
        heads = [shift(Th, add(K3, mul(i, K4))) for i in range(1, 2 * (k + 1) - z + 1)]
    return union(*stems, bridge, *heads)


def even_case(u, flip):
    W1 = at.phase(u) == 1
    if W1 and not flip:
        return '10'
    if W1 and flip:
        return '11'
    if not W1 and not flip:
        return '00'
    return '01'


def even_table(case, s, p, q):
    """[K1,K2,K3,K4] of eq:l_correction_even (lines 3566-3588) with s the last letter of u (1 or 2)."""
    vp1, vq1, vp2, vq2 = V1o(p), V1e(q), V2(p), V2(q)
    if case == '10':
        K1, K2, K4 = vp1, vp1, vp2
        K3 = add(sub(vq1, vp1), add(sub(vq2, vp2), vq1)) if s == '2' else sub(vq1, vp1)
    elif case == '00':
        K1, K2, K4 = neg(vp1), neg(vq1), vp2
        K3 = sub(vq2, vp2) if s == '2' else sub(vp1, vq1)
    elif case == '11':
        K1, K2, K4 = neg(vp1), add(neg(vq1), sub(vp1, vq1)), neg(vp2)
        K3 = add(sub(vq2, vp2), vq1) if s == '2' else (0, 0)
    else:
        K1, K2, K4 = vp1, add(vp1, sub(vp2, vq2)), neg(vp2)
        K3 = add(sub(vq2, vp2), neg(vp1), vq1) if s == '2' else (0, 0)
    return K1, K2, K3, K4


def even_L(u, x, flip, elong, Tp, Tq, Th, variant='c'):
    """The even L-correction for x = u 3^k: stems T(p2), bridge T(q2), heads T-hat(p2)."""
    p, q = at.parents_at(u)
    k = len(x) - len(u)
    K1, K2, K3, K4 = even_table(even_case(u, flip), u[-1], p, q)
    z = 0 if elong else 1
    stems = [shift(Tp, mul(j, K1)) for j in range(k + 1)]
    if variant == 'c':
        base = add(mul(k, K1), K2)
        bridge = shift(Tq, base)
        heads = [shift(Th, add(base, K3, mul(i, K4))) for i in range(1, 2 * (k + 1) - z + 1)]
    else:
        bridge = shift(Tq, K2)
        heads = [shift(Th, add(K3, mul(i, K4))) for i in range(1, 2 * (k + 1) - z + 1)]
    return union(*stems, bridge, *heads)


# ---------- comparison with the constructor ----------

def compare(P, C, variant):
    results = {}
    for (parity, x, side, length), cons in sorted(C.items()):
        if cons is None:
            continue
        if parity == 'odd':
            u = x.rstrip('2')
            if not u or u[-1] not in '13':
                continue
            tiles = P[u]
            Tp, Tq, Th = tiles['stdRetOdd'], tiles['stdRetEven'], tiles['altRetEven']
            cand = odd_L(u, x, side == 'L', length == 'long', Tp, Tq, Th, variant)
            label = 'odd ' + odd_case(u, side == 'L')
        else:
            u = x.rstrip('3')
            if not u or u[-1] not in '12':
                continue
            tiles = P[u]
            Tp, Tq, Th = tiles['stdRetOdd'], tiles['stdRetEven'], tiles['altRetOdd']
            cand = even_L(u, x, side == 'L', length == 'long', Tp, Tq, Th, variant)
            label = 'even ' + even_case(u, side == 'L')
        ok = nc.normalised(cand) == nc.normalised(cons)
        same_shape = len(cand) == len(cons)
        results.setdefault(label, []).append((x, side, length, ok, same_shape))
    return results


def main(argv):
    P, C = parse_lcorr(argv[0])
    for variant in ('c', 'lit'):
        res = compare(P, C, variant)
        print('variant', variant)
        total = bad = 0
        for label in sorted(res):
            rows = res[label]
            fails = [r for r in rows if not r[3]]
            total += len(rows)
            bad += len(fails)
            first = fails[0] if fails else None
            print('  %-12s %2d checked, %2d differ (up to translation); first differing: %s' %
                  (label, len(rows), len(fails), first[:3] if first else '-'))
        print('  total %d checked, %d differ' % (total, bad))


if __name__ == '__main__':
    main(sys.argv[1:])
