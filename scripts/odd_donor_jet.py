"""Does the odd alternate tile of a prefix p equal its quarter-turn target Q(p) placed by a translation T and a slope J?

Q(p)(x) = H_{swap p}((-x2, x1 - 1)) + h0(x), the odd target of task 46. The test is
  D(y) = Q(p)(y - T) + J . y + c  for every site y of D, with one constant c.
"""
import sys
import ordinary_tile_check as otc
import alt_plane_check as apc

ns = otc.load_proto()
standard, h0, swap, Frame = ns["standard"], ns["h0"], ns["swap"], ns["Frame"]


def H_of(u):
    F = standard(tuple(u))[0]
    fr = Frame(list(u))
    sig = (2 * fr.eps * fr.D, 2 * fr.eps * fr.N)
    return lambda z: -((-(F(z) + F((z[0] + sig[0], z[1] + sig[1])))) // 2)


def Q_of(p):
    Hs = H_of(swap(list(p)))
    return lambda x: Hs((-x[1], x[0] - 1)) + h0(*x)


def placed_fit(sites, target, Tbox, Jbox):
    hits = []
    for J in [(j1, j2) for j1 in Jbox for j2 in Jbox]:
        for a in Tbox:
            for b in Tbox:
                c = None
                ok = True
                for (y, dy) in sites:
                    k = dy - (target((y[0] - a, y[1] - b)) + J[0] * y[0] + J[1] * y[1])
                    if c is None:
                        c = k
                    elif k != c:
                        ok = False
                        break
                if ok:
                    hits.append(((a, b), J, c))
    return hits


if __name__ == "__main__":
    words = apc.parse_log(apc.DATA)
    byw = {tuple(e["word"]): e for e in words}
    Tb = range(-int(sys.argv[1]), int(sys.argv[1]) + 1)
    Jb = range(-int(sys.argv[2]), int(sys.argv[2]) + 1)
    for p in [tuple(x) for x in eval(sys.argv[3])]:
        D = byw[p]["odd"]
        hits = placed_fit(D, Q_of(list(p)), Tb, Jb)
        print(p, "phase", sum(1 for d in p if d == 1) % 2, "placed fits:", len(hits), hits[:3], flush=True)
