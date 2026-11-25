"""Link check at 3^k: the W1 policy of standardField(3^k) against the Retained sets.
For every native centre c (raw sites of the B1 tile = NativeP), lap(c) = G(incomingNeg c) - G c + G(incomingPos c) - G c with the
extension of w1_field_3k.py. Quota of the policy: lap = -1 (black) retains both parity-axis inputs; lap = 0 (white) retains at
least one. The check compares with the retained parity-axis unit directions of the Q_minus rule (w1_bulk_gate.py) and of the
Q_plus rule (w1_plus_gate.py)."""
import sys
from collections import Counter
sys.path.insert(0, 'scripts')
import importlib.util
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
W = load('w', 'scripts/w1_field_3k.py')
B = load('b', 'scripts/w1_bulk_gate.py')
P = load('p', 'scripts/w1_plus_gate.py')

def even(x): return (x[0] + x[1]) % 2 == 0
def inc_neg(x): return (x[0] - 1, x[1]) if even(x) else (x[0], x[1] - 1)
def inc_pos(x): return (x[0] + 1, x[1]) if even(x) else (x[0], x[1] + 1)

def run(k):
    f = W.Field(k); d = f.d
    edgesMinus = B.make(d)
    stats = Counter(); viol = []
    for c in f.raw:
        g = f.F(c)
        lap = (f.F(inc_neg(c)) - g) + (f.F(inc_pos(c)) - g)
        par = 'even' if even(c) else 'odd'
        # retained parity-axis unit directions
        axis = [(-1, 0), (1, 0)] if even(c) else [(0, -1), (0, 1)]
        Rm = [e for e in axis if e in edgesMinus(c[0], c[1])[0]]
        Rp = [e for e in axis if P.edgePlus(d, c[0], c[1], *e)]
        stats[(lap, par)] += 1
        if lap == -1:
            if len(Rm) != 2: viol.append(('black-minus', c, Rm))
            if len(Rp) != 2: viol.append(('black-plus', c, Rp))
        elif lap == 0:
            if len(Rm) == 0: viol.append(('white-minus', c))
            if len(Rp) == 0: viol.append(('white-plus', c))
        else:
            viol.append(('lap', c, lap))
    return d, stats, viol

if __name__ == '__main__':
    for k in range(0, 7):
        d, stats, viol = run(k)
        kinds = Counter(v[0] for v in viol)
        print('k=%d d=%d centres %d  (lap,parity) %s  violations %s' % (k, d, sum(stats.values()), dict(stats), dict(kinds)), viol[:3], flush=True)
