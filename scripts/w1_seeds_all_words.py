"""Task 50 numerics: the seeds of SeedFields for ALL words of length <= MAXLEN (proper and pure), on their lines.

For a word w with child n/d (L = d + n, parents dp = (d+n)/2, np = (d-n)/2 of the odd conjugate):
  even seed  (even_zero):  F = 0 at even sites with t = 2 - L                     (t = n x - d y)
  odd zero   (odd_zero):   f = quarterTurn(F) = F(-x2, x1-1) + h0(x) = 0 at even x with np x1 - dp x2 = 1 - d
  bottom h0  (derived):    F = h0 at odd sites with s = 2 - 3d + n                  (s = L x + (d-n) y)
Points are sampled on each line in a window of y in [-Y, Y]. Words that fail to evaluate are reported, not skipped silently.
"""
import itertools
import sys
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, h0

MAXLEN = int(sys.argv[1]) if len(sys.argv) > 1 else 3

def kind(w):
    if all(x == 3 for x in w):
        return 'pure3'
    if all(x == 2 for x in w):
        return 'pure2'
    return 'proper'

def run(w):
    F, _ = standard(w)
    fr = Frame(w)
    n, d, L, T = fr.n, fr.d, fr.L, fr.T
    if (n + d) % 2:
        return {'skip_odd_child': True}
    dp, np_ = (d + n) // 2, (d - n) // 2
    Y = 2 * T + 2 * L
    st = {'even': [0, 0], 'odd_zero': [0, 0], 'bottom': [0, 0]}
    def qt(x):
        return F((-x[1], x[0] - 1)) + h0(x[0], x[1])
    for y in range(-Y, Y + 1):
        num = (2 - L) + d * y
        if num % n == 0:
            x = num // n
            if (x + y) % 2 == 0:
                st['even'][0] += 1
                if F((x, y)) != 0:
                    st['even'][1] += 1
        num = (1 - d) + dp * y
        if num % np_ == 0:
            x = num // np_
            if (x + y) % 2 == 0:
                st['odd_zero'][0] += 1
                if qt((x, y)) != 0:
                    st['odd_zero'][1] += 1
        num = (2 - 3 * d + n) - (d - n) * y
        if num % L == 0:
            x = num // L
            if (x + y) % 2 == 1:
                st['bottom'][0] += 1
                if F((x, y)) != h0(x, y):
                    st['bottom'][1] += 1
    return {'n': n, 'd': d, 'st': st}

if __name__ == '__main__':
    tot = {}
    for L in range(1, MAXLEN + 1):
        for w in itertools.product((1, 2, 3), repeat=L):
            k = kind(w)
            try:
                res = run(w)
            except Exception as e:
                tot.setdefault(k, {}).setdefault('failed', 0)
                tot[k]['failed'] += 1
                print('FAILED', ''.join(map(str, w)), type(e).__name__, str(e)[:80], flush=True)
                continue
            if 'skip_odd_child' in res:
                tot.setdefault(k, {}).setdefault('skipped', 0)
                tot[k]['skipped'] += 1
                continue
            t = tot.setdefault(k, {'words': 0, 'pts': [0, 0, 0, 0, 0, 0], 'bad': 0})
            t['words'] += 1
            s = res['st']
            t['pts'] = [t['pts'][0] + s['even'][0], t['pts'][1] + s['even'][1],
                        t['pts'][2] + s['odd_zero'][0], t['pts'][3] + s['odd_zero'][1],
                        t['pts'][4] + s['bottom'][0], t['pts'][5] + s['bottom'][1]]
            t['bad'] += s['even'][1] + s['odd_zero'][1] + s['bottom'][1]
            if s['even'][1] or s['odd_zero'][1] or s['bottom'][1]:
                print('BAD', ''.join(map(str, w)), res['n'], res['d'], s, flush=True)
    for k, v in tot.items():
        print(k, v, flush=True)
