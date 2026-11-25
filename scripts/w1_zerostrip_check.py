"""Task 59 numerics: the zero-strip, even-line and odd-seed fields at a general proper word u (Lean convention).

For u with child n/d (odd), the Lean values are parentN u = (d - n)/2 and parentD u = (d + n)/2 (the odd parent of the word
whose conjugate is u). The fields, with F = standard(u) and quarterTurn F (x) = F(Zx) + h0(x), Zx = (-x2, x1 - 1):
  zeroStripInterval: quarterTurn F (x) = 0 for 1 - Du <= Nu x1 - Du x2 <= Nu + 2Du - 1;
  zeroEvenLine:      quarterTurn F (x) = 0 for x even with Nu x1 - Du x2 = -Du;
  odd seed (SeedFields.odd_zero): quarterTurn F (x) = 0 for x even with Nu x1 - Du x2 = 1 - (Du + Nu).
Odd lower extension (hlow): F = h0 on odd sites with s in [2 - 3d + n, 1 - 2d].
Use with: python3 scripts/w1_zerostrip_check.py   (all counts should be zero failures).
"""
import itertools, sys
sys.path.insert(0, 'scripts')
from permit_local import standard, Frame, h0

Z = lambda x: (-x[1], x[0] - 1)

def run(u, R_extra=6):
    fr = Frame(u)
    n, d = fr.n, fr.d
    Nu, Du = (d - n) // 2, (d + n) // 2
    G, _ = standard(tuple(u))
    f = lambda x: G(Z(x)) + h0(*x)
    R = 2 * d + R_extra
    counts = {'band': [0, 0], 'even': [0, 0], 'seed': [0, 0], 'lower': [0, 0]}
    for x1 in range(-R, R + 1):
        for x2 in range(-R, R + 1):
            x = (x1, x2)
            tp = Nu * x1 - Du * x2
            par = (x1 + x2) % 2
            if 1 - Du <= tp <= Nu + 2 * Du - 1:
                counts['band'][0] += 1
                counts['band'][1] += f(x) != 0
            if par == 0 and tp == -Du:
                counts['even'][0] += 1
                counts['even'][1] += f(x) != 0
            if par == 0 and tp == 1 - (Du + Nu):
                counts['seed'][0] += 1
                counts['seed'][1] += f(x) != 0
            y = (x1, x2)
            s = (d + n) * y[0] + (d - n) * y[1]
            if (y[0] + y[1]) % 2 == 1 and 2 - 3 * d + n <= s <= 1 - 2 * d:
                counts['lower'][0] += 1
                counts['lower'][1] += G(y) != h0(*y)
    return counts

if __name__ == '__main__':
    totals = {'band': [0, 0], 'even': [0, 0], 'seed': [0, 0], 'lower': [0, 0]}
    for L_ in (1, 2, 3):
        for u in itertools.product((1, 2, 3), repeat=L_):
            if all(x == 3 for x in u) or all(x == 2 for x in u):
                continue
            c = run(u)
            for k in totals:
                totals[k][0] += c[k][0]
                totals[k][1] += c[k][1]
    print('(points checked, failures):', totals)
