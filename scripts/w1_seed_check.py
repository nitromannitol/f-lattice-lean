"""Task 49 numerics: the named seeds of the W1 strips, on their exact lines (not the whole strips).

For every proper word of length <= MAXLEN (not all-2) with standard field F and native h0 (permit_local):
  even seed:   F = 0 at even sites with t = 2 - L        (t = n x - d y, L = d + n)     [named hypothesis of even_zero_lower]
  odd bottom:  F = h0 at odd sites with s = 2 - 3d + n   (s = L x + (d - n) y)          [named hseed of lower_odd_h0]
  odd top:     F = h0 at odd sites with s = 3d + n - 2   (the I-reflection partner of the bottom, hIsym)
Points are found on each line by solving the linear equation for x in a window of y in [-Y, Y].
"""
import sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, proper_words, h0

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 3

def run(w):
    F, _ = standard(w)
    fr = Frame(w)
    n, d, L, T = fr.n, fr.d, fr.L, fr.T
    Y = 2 * T + 2 * L
    stats = {'even_seed': [0, 0], 'odd_bottom': [0, 0], 'odd_top': [0, 0]}
    for y in range(-Y, Y + 1):
        num = (2 - L) + d * y
        if num % n == 0:
            x = num // n
            if (x + y) % 2 == 0:
                stats['even_seed'][0] += 1
                if F((x, y)) != 0:
                    stats['even_seed'][1] += 1
        for name, cs in (('odd_bottom', 2 - 3 * d + n), ('odd_top', 3 * d + n - 2)):
            num = cs - (d - n) * y
            if num % L == 0:
                x = num // L
                if (x + y) % 2 == 1:
                    stats[name][0] += 1
                    if F((x, y)) != h0(x, y):
                        stats[name][1] += 1
    return ''.join(map(str, w)), n, d, stats

if __name__ == '__main__':
    tot_bad = 0
    words = 0
    for w in proper_words(MAXLEN):
        if all(x == 2 for x in w):
            continue
        word, n, d, st = run(w)
        words += 1
        bad = sum(v[1] for v in st.values())
        tot_bad += bad
        print(word, 'n=%d d=%d' % (n, d), st, flush=True)
    print('words', words, 'total bad points', tot_bad)
