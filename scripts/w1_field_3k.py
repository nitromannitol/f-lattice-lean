"""Explicit extension of reciprocalField k = standardField(3^k) (task 118, W1 base; lead's option (b)).
Transcribes, from the Lean definitions: BaseMask.stairEven (raw sites: mem_stairEven_raw_iff; values: stairEvenValue, StairEvenCorner),
Fraction.mk 1 d (periodDenominator = d^2+2d-1, modifiedDeck = ((d,1), (1-d,1+d)) for d odd, transverseGrade = d*y - x),
stairEvenConstantV d = -chooseTwo(d+1) - d, periodIncrement (constantU = 0, constantV = stairEvenConstantV), chooseTwo n = n(n-1)/2.
F(z) = raw(r) + periodIncrement(r; i, j) for z = r + i*K + j*T with r a raw site. Checks: all representatives agree; raw values;
both generator periods on a window. Then the laplacian of the policy at the native centres and the parity classes, against the
Q_minus and Q_plus retained sets of w1_bulk_gate.py and w1_plus_gate.py."""
import sys
from collections import Counter
sys.path.insert(0, 'scripts')
import importlib.util
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

def chooseTwo(n): return n * (n - 1) // 2

class Field:
    def __init__(self, k):
        self.k = k; d = 2 * k + 3; self.d = d
        self.K = (d, 1); self.T = (1 - d, 1 + d)
        self.Dn = d * d + 2 * d - 1
        self.cV = -chooseTwo(d + 1) - d
        self.raw = {}
        for c in range(2 - d, d + 1):
            for r in range(0, d + 2):
                corner = (c, r) in [(0, 0), (2, d + 1)]
                if corner or (1 <= c + r <= d + 2):
                    self.raw[(c, r)] = self.raw_value((c, r))

    def raw_value(self, p):
        d = self.d; c, r = p
        corner = 1 if (p in [(0, 0), (2, d + 1)]) else 0
        return -(r * (r - 1) // 2) + min(c - 1, 0) + corner

    def grade(self, s):
        return self.d * s[1] - s[0]

    def value(self, z):
        """F(z) from every raw representative; returns (value, number of representatives, all agree)."""
        d = self.d; Dn = self.Dn
        vals = []
        for r in self.raw:
            dx = z[0] - r[0]; dy = z[1] - r[1]
            num = d * dy - dx
            if num % Dn: continue
            j = num // Dn
            i = dy - j * (1 + d)
            # check the decomposition
            assert dx == i * d + j * (1 - d) and dy == i + j * (d + 1)
            v = self.raw[r] + i * 0 + j * (self.cV - self.grade(r)) - Dn * chooseTwo(j)
            vals.append(v)
        assert vals, ('no representative', z)
        return vals[0], len(vals), all(v == vals[0] for v in vals)

    def F(self, z):
        v, n, agree = self.value(z)
        assert agree, ('representatives disagree', self.k, z)
        return v

def check_field(k, window=6):
    f = Field(k); d = f.d
    bad = []
    for r, h in f.raw.items():
        v, n, agree = f.value(r)
        if v != h or not agree: bad.append(('raw', r, v, h, agree))
    for x in range(-window - d, window + d):
        for y in range(-window, window + d):
            z = (x, y)
            v, n, agree = f.value(z)
            if not agree: bad.append(('disagree', z))
            zk = (x + f.K[0], y + f.K[1]); zt = (x + f.T[0], y + f.T[1])
            if f.value(zk)[0] != v: bad.append(('kernel', z))
            if f.value(zt)[0] != v - f.grade(z) + f.cV: bad.append(('transverse', z))
    return f, bad

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'check'
    for k in range(0, 7):
        f, bad = check_field(k)
        print('k=%d d=%d raw sites %d violations %d' % (k, f.d, len(f.raw), len(bad)), bad[:3], flush=True)
