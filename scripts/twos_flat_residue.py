import sys
sys.path.insert(0, 'scripts')
from twos_signed_e import Twos, add, neg
sys.setrecursionlimit(20000)

def run(K):
    t = Twos(K)
    cl = t.clauses(); forced, _ = t.forced(cl)
    free_keys = {t.key(v) for v in t.H() + t.V()}
    a = t.a; Rf = (a, 3 * a - 2)
    for eta in (1, -1):
        dirs = t.dirs(eta, forced)
        succ = {r: set() for r in range(t.T)}
        for r in range(t.T):
            c = t.rep(r)
            for i in t.retained(dirs, c):
                if t.chain(eta, i) == t.chain(eta, c):
                    succ[r].add(t.key(i))
        rank, onstack = {}, set()
        def visit(r):
            if r in rank: return rank[r]
            if r in onstack: raise ValueError('cycle')
            onstack.add(r); v = 0
            for s in succ[r]: v = max(v, visit(s) + 1)
            onstack.discard(r); rank[r] = v; return v
        try:
            for r in range(t.T): visit(r)
            acyc = True
        except ValueError:
            acyc = False
        # reflection mismatches by class
        dm = t.dirs(-eta, forced)
        mm_free = mm_forced = 0
        for r in range(t.T):
            c = t.rep(r)
            s = add(Rf, neg(c))
            if t.retained(dm, s) != {add(Rf, neg(i)) for i in t.retained(dirs, c)}:
                if r in free_keys or t.key(c) in free_keys: mm_free += 1
                else: mm_forced += 1
        print('K=%d eta=%+d Phi-flat residue graph acyclic: %s, witness max %s, reflection mismatches (sign -eta) on free classes %d, on forced classes %d'
              % (K, eta, acyc, max(rank.values()) if acyc else '-', mm_free, mm_forced))
        if acyc:
            # R = M*Phi + r, r = witness on classes; strictness on all selected edges
            rmin, rmax = min(rank.values()), max(rank.values())
            M = 1 + (rmax - rmin)
            bad = 0; edges = 0
            for r in range(t.T):
                c = t.rep(r)
                for i in t.retained(dirs, c):
                    edges += 1
                    Rc = M * t.chain(eta, c) + rank[t.key(c)]
                    Ri = M * t.chain(eta, i) + rank[t.key(i)]
                    if not Ri < Rc: bad += 1
            print('   strict R = M*Phi + r on all %d selected edges: failures %d (M=%d, r in [%d,%d])' % (edges, bad, M, rmin, rmax))

for K in [int(x) for x in sys.argv[1:]] or [1, 2, 3, 4]:
    run(K)
