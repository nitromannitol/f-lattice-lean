"""Bulk gate of Q_minus, all native sources (task 118, W1 base, step (ii)-(iii)).
Re-implements the edge predicate of .work/fields/canonical/pure3_initialization/prove_rank.py (star, lap, corr, whites, hits)
and checks, for every native source p and every retained direction e (edge(p, e) true), that every rank of p+e is below rank(p).
Reports, per family of the source, the retained directions and the number of violations."""
import importlib.util
from collections import Counter, defaultdict
spec = importlib.util.spec_from_file_location('w', 'scripts/w1_free_root_gate.py')
w = importlib.util.module_from_spec(spec); spec.loader.exec_module(w)
f, ALIASES, shift, native, isrep, ranks = w.f, w.ALIASES, w.shift, w.native, w.isrep, w.ranks

def make(d):
    def mn(a): return min(a, 0)
    def corr(X, Y): return mn(X - 1) + (1 if (X, Y) in [(0, 0), (2, d + 1)] else 0)
    def star(X, Y):
        if not native(d, X, Y): return False
        if (X + Y) % 2 == 0: return native(d, X - 1, Y) and native(d, X + 1, Y)
        return native(d, X, Y - 1) and native(d, X, Y + 1)
    def lap(X, Y):
        if (X + Y) % 2 == 0: return corr(X - 1, Y) + corr(X + 1, Y) - 2 * corr(X, Y)
        return -1 + corr(X, Y - 1) + corr(X, Y + 1) - 2 * corr(X, Y)
    def presc(a, b):  # prescribed direction of a free point (hx,hy) / (vx,vy)
        if (a + b) % 2 == 0: return (-1, 0)
        if f.isfree(d, a, b) and f.H(a, b) if False else (b == 0 and 1 <= a <= d): return (0, 1) if a == d else (0, -1)
        return (0, 1)
    def edges(X, Y):
        """retained directions from (X,Y): list of (dx,dy)"""
        par0 = (X + Y) % 2 == 0
        dirs = [(-1, 0), (1, 0)] if par0 else [(0, -1), (0, 1)]
        whites = []
        hits = set()
        has_free_translate = any(f.isfree(d, *shift(d, X, Y, i, j)) for i, j in ALIASES)
        for i, j in ALIASES:
            a, b = shift(d, X, Y, i, j)
            if f.isfree(d, a, b):
                whites.append(('free', i, j))
                hits.add(presc(a, b))
            if not has_free_translate:
                cg = star(a, b) and lap(a, b) == 0 and (a + b) % 2 == 0 and (a <= 0 or a >= 2)
                if cg:
                    whites.append(('cg', i, j))
                    hits.add((-1 if a <= 0 else 1, 0))
        if not whites:
            return dirs, 'none'
        return [e for e in dirs if e in hits], 'white'
    return edges

def family(d, X, Y):
    return f.family(d, X, Y)

if __name__ == '__main__':
    for d in range(3, 16, 2):
        edges = make(d)
        stat = Counter(); viol = []; nrun = 0
        for X in range(2 - d, d + 1):
            for Y in range(0, d + 2):
                if not native(d, X, Y) or f.isfree(d, X, Y): continue
                fam = family(d, X, Y)
                ds, kind = edges(X, Y)
                rp = ranks(d, X, Y)
                vals = set(r for _, _, r in rp)
                if len(vals) != 1: viol.append(('multi', X, Y)); continue
                vp = vals.pop()
                for e in ds:
                    nrun += 1
                    rt = [r for _, _, r in ranks(d, X + e[0], Y + e[1])]
                    stat[(fam, kind, e)] += 1
                    if any(r >= vp for r in rt): viol.append(((X, Y), e, rt, vp))
        print('d=%d retained edges %d violations %d' % (d, nrun, len(viol)), viol[:3])
        if d == 9:
            for k in sorted(stat): print('   ', k, stat[k])
