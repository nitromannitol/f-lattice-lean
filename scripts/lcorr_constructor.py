"""Task 35: the constructor's L-correction as the TeX shape plus the three constructor-side terms found numerically:
  (a) the bridge nudge of correctionPieces: for the odd parity with an all-3 ancestor the bridge (cross) tile moves by
      (0,-1) (non-flip) or (1,-1) (flip); for the even parity with an all-2 ancestor and flip it moves by (1,1);
  (b) the head restoration (restoreAlternate / alternateRestoration) of the odd corrections: the retained alternate tile
      moves by r(u), where r(1) = (-2,-1) and r(31) = (-4,-1), and r(u) = 0 for the other ancestors of length <= 2 (fitted to
      the outputs; the birth-dependent formula alternateRestoration is not evaluated here).
Uses the corrected table entries (lcorr_ctable): odd 11 K1, odd 00 K3, even 11 K2 as in the constructor's correctionJets.
"""
import sys
import lcorr_tex as L
import lcorr_ctable as CT
import native_compare as nc

RESTORE = {'1': (-2, -1), '31': (-4, -1)}


def odd_cons(u, x, flip, elong, Tp, Tq, Th):
    p, q = L.at.parents_at(u)
    k = len(x) - len(u)
    K1, K2, K3, K4 = CT.odd_ctable(L.odd_case(u, flip), p, q)
    z = 0 if elong else 1
    stems = [L.shift(Tq, L.mul(j, K1)) for j in range(k + 1)]
    base = L.add(L.mul(k, K1), K2)
    nudge = (0, -1) if not flip else (1, -1)
    if set(u) == {'3'} or (u and all(d == '3' for d in u)):
        bridge = L.shift(Tp, L.add(base, nudge))
    else:
        bridge = L.shift(Tp, base)
    r = RESTORE.get(u, (0, 0))
    heads = [L.shift(Th, L.add(base, K3, L.mul(i, K4), r)) for i in range(1, 2 * (k + 1) - z + 1)]
    return L.union(*stems, bridge, *heads)


def even_cons(u, x, flip, elong, Tp, Tq, Th):
    p, q = L.at.parents_at(u)
    k = len(x) - len(u)
    K1, K2, K3, K4 = CT.even_ctable(L.even_case(u, flip), u[-1], p, q)
    z = 0 if elong else 1
    stems = [L.shift(Tp, L.mul(j, K1)) for j in range(k + 1)]
    base = L.add(L.mul(k, K1), K2)
    if flip and all(d == '2' for d in u):
        bridge = L.shift(Tq, L.add(base, (1, 1)))
    else:
        bridge = L.shift(Tq, base)
    heads = [L.shift(Th, L.add(base, K3, L.mul(i, K4))) for i in range(1, 2 * (k + 1) - z + 1)]
    return L.union(*stems, bridge, *heads)


def cand(P, parity, x, flip, elong):
    if parity == 'odd':
        u = x.rstrip('2')
        t = P[u]
        return odd_cons(u, x, flip, elong, t['stdRetOdd'], t['stdRetEven'], t['altRetEven'])
    u = x.rstrip('3')
    t = P[u]
    return even_cons(u, x, flip, elong, t['stdRetOdd'], t['stdRetEven'], t['altRetOdd'])


def main(path):
    P, Cc = L.parse_lcorr(path)
    total = bad = 0
    fails = []
    for (parity, x, side, length), cons in sorted(Cc.items()):
        if cons is None:
            continue
        u = x.rstrip('2') if parity == 'odd' else x.rstrip('3')
        if not u or u[-1] not in ('13' if parity == 'odd' else '12'):
            continue
        total += 1
        ok = nc.normalised(cand(P, parity, x, side == 'L', length == 'long')) == nc.normalised(cons)
        if not ok:
            bad += 1
            fails.append((parity, x, side, length))
    print('constructor-mode candidate: %d outputs checked, %d differ (up to translation)' % (total, bad))
    print('  failing:', fails[:6])


if __name__ == '__main__':
    main(sys.argv[1])
