import sys
sys.path.insert(0, 'scripts')
import twos_signed_e as ts
from collections import Counter
from twos_signed_e import Twos, add, neg, ip

def analyse(K):
    t = Twos(K)
    cl = t.clauses(); forced, _ = t.forced(cl)
    a = t.a
    Rf = (a, 3 * a - 2)
    c0 = a * a + a - 1
    # reflection of the field
    refl_bad = 0
    for x in range(-3, 4):
        for y in range(-3, 4):
            z = (x, y)
            if t.F(add(Rf, neg(z))) != t.F(z) - (t.n * x - t.d * y) - c0:
                refl_bad += 1
    print('K=%d field reflection F(R-z)=F(z)-t(z)-(a^2+a-1): failures %d' % (K, refl_bad))
    for eta in (1, -1):
        U, V = (t.d, t.n), (-2, 2 * a)
        chars = set()
        for z in [(0, 0), (1, 2), (-2, 3)]:
            chars.add(('U', t.chain(eta, add(z, U)) - t.chain(eta, z)))
            chars.add(('V', t.chain(eta, add(z, V)) - t.chain(eta, z)))
        flat, drop, alld = Counter(), 0, Counter()
        dirs = t.dirs(eta, forced)
        for r in range(t.T):
            c = t.rep(r)
            for i in t.retained(dirs, c):
                e = add(i, neg(c))
                alld[e] += 1
                if t.chain(eta, i) == t.chain(eta, c):
                    flat[e] += 1
                else:
                    drop += 1
        feas = [(al, be) for al in range(-12, 13) for be in range(-12, 13)
                if all(al * e[0] + be * e[1] < 0 for e in flat)]
        print('  eta=%+d chain characters %s; selected displacements %s; Phi-flat displacements %s; Phi-drop edges %d'
              % (eta, sorted(chars), sorted(alld), sorted(flat), drop))
        print('     integer linear L=(al,be) with L(e)<0 on all Phi-flat displacements, |al|,|be|<=12: %s'
              % (feas[:12] if feas else 'NONE'))
        # reflection: retained_{eta'}(R - c) against R - retained_eta(c), both signs of eta'
        for etap in (eta, -eta):
            dp = t.dirs(etap, forced)
            bad = 0
            for r in range(t.T):
                c = t.rep(r)
                s = add(Rf, neg(c))
                lhs = t.retained(dp, s)
                rhs = {add(Rf, neg(i)) for i in t.retained(dirs, c)}
                if lhs != rhs:
                    bad += 1
            print('     reflection: policy_%+d(R-c) == R - policy_%+d(c) : %d failures of %d' % (etap, eta, bad, t.T))

if __name__ == '__main__':
    for K in [int(x) for x in sys.argv[1:]] or [1, 2, 3, 4]:
        analyse(K)
