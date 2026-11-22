"""Task 35 diagnostic: for each L-correction that differs from the constructor (variant c), the translations r of the
head copies only (stems and bridge fixed) that make the TeX union equal the constructor output (up to translation)."""
import sys
import lcorr_tex as L
import native_compare as nc


def head_shifts(cand_parts, cons):
    stems, bridge, heads = cand_parts
    target = nc.normalised(cons)
    found = []
    for rx in range(-14, 15):
        for ry in range(-14, 15):
            Hs = frozenset().union(*[L.shift(h, (rx, ry)) for h in heads]) if heads else frozenset()
            T = stems | bridge | Hs
            if nc.normalised(T) == target:
                found.append((rx, ry))
    return found


def main(path):
    P, C = L.parse_lcorr(path)
    for (parity, x, side, length), cons in sorted(C.items()):
        if cons is None:
            continue
        flip, elong = side == 'L', length == 'long'
        if parity == 'odd':
            u = x.rstrip('2')
            if not u or u[-1] not in '13':
                continue
            t = P[u]
            Tp, Tq, Th = t['stdRetOdd'], t['stdRetEven'], t['altRetEven']
            k = len(x) - len(u)
            K1, K2, K3, K4 = L.odd_table(L.odd_case(u, flip), *L.at.parents_at(u))
            base = L.add(L.mul(k, K1), K2)
            stems = frozenset().union(*[L.shift(Tq, L.mul(j, K1)) for j in range(k + 1)])
            bridge = L.shift(Tp, base)
            heads = [L.shift(Th, L.add(base, K3, L.mul(i, K4))) for i in range(1, 2 * (k + 1) - (0 if elong else 1) + 1)]
            label = 'odd ' + L.odd_case(u, flip)
        else:
            u = x.rstrip('3')
            if not u or u[-1] not in '12':
                continue
            t = P[u]
            Tp, Tq, Th = t['stdRetOdd'], t['stdRetEven'], t['altRetOdd']
            k = len(x) - len(u)
            K1, K2, K3, K4 = L.even_table(L.even_case(u, flip), u[-1], *L.at.parents_at(u))
            base = L.add(L.mul(k, K1), K2)
            stems = frozenset().union(*[L.shift(Tp, L.mul(j, K1)) for j in range(k + 1)])
            bridge = L.shift(Tq, base)
            heads = [L.shift(Th, L.add(base, K3, L.mul(i, K4))) for i in range(1, 2 * (k + 1) - (0 if elong else 1) + 1)]
            label = 'even ' + L.even_case(u, flip)
        if nc.normalised(stems | bridge | frozenset().union(*heads)) == nc.normalised(cons):
            continue
        sols = head_shifts((stems, bridge, heads), cons)
        print('%-9s %-3s %-6s %-5s head shifts that fit: %s' % (label, x, side, length, sols[:4] if sols else 'none in box'))


if __name__ == '__main__':
    main(sys.argv[1])
