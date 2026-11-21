"""Random longer admissible pairs: window bound, packing P, gap clause A, and |T| <= det."""
import random
import sys
from collections import Counter

import window_scan as ws


def random_admissible(n_max, rng):
    """Draw random words that satisfy `admissible`, by palindromic constructions, lengths up to n_max."""
    while True:
        kind = rng.choice(['a', 'b', 'c'])
        if kind == 'a':
            n = rng.randint(1, n_max)
            half = [rng.choice((0, 1)) for _ in range((n + 1) // 2)]
            w = half + half[::-1][(n % 2):]
            w[0] = 0
            w[-1] = 0
            w = w[:]
            # re-mirror after fixing ends so it stays a palindrome
            w = w[: (n + 1) // 2] + w[: (n + 1) // 2][::-1][(n % 2):]
            if len(w) == n and ws.admissible(w):
                return w
        elif kind == 'b':
            m = rng.randint(0, max(0, n_max - 4))
            half = [rng.choice((0, 1)) for _ in range((m + 1) // 2)]
            p = half + half[::-1][(m % 2):]
            w = [0, 0, 1] + p + [0]
            if len(w) <= n_max and ws.admissible(w):
                return w
        else:
            m = rng.randint(0, max(0, n_max - 4))
            half = [rng.choice((0, 1)) for _ in range((m + 1) // 2)]
            p = half + half[::-1][(m % 2):]
            w = [0] + p + [0, 0, 0]
            if len(w) <= n_max and ws.admissible(w):
                return w


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    n_max = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    rng = random.Random(seed)
    pool1 = [random_admissible(n_max, rng) for _ in range(3000)]
    pool2 = [[ws.mulI(x) for x in random_admissible(n_max, rng)] for _ in range(3000)]
    simple = 0
    win_fail = []
    P_fail = []
    A_fail = []
    area_gt_det = []
    worst = (0.0, None)
    for _ in range(trials):
        w1 = rng.choice(pool1)
        w2 = rng.choice(pool2)
        r = ws.analyse(w1, w2)
        if r is None or r.get('bad'):
            continue
        simple += 1
        ratio = max(r['spread1'], r['spread2']) / r['Dabs']
        if ratio > worst[0]:
            worst = (ratio, r)
        if not r['window_ok']:
            win_fail.append(r)
        if not r['P_ok']:
            P_fail.append(r)
        if not r['A_ok']:
            A_fail.append(r)
        if r['cells'] > r['Dabs']:
            area_gt_det.append(r)
    print('seed', seed, 'n_max', n_max, 'trials', trials, 'simple tiles', simple)
    print('window fails', len(win_fail), 'P fails', len(P_fail), 'A fails', len(A_fail),
          '|T|>det', len(area_gt_det))
    if worst[1] is not None:
        r = worst[1]
        print('worst ratio', round(worst[0], 4), 'len w1', len(r['w1']), 'len w2', len(r['w2']),
              'D', r['D'], 'cells', r['cells'])
    if P_fail:
        r = P_fail[0]
        print('P counterexample: w1', r['w1'], 'w2', r['w2'])
    if A_fail:
        r = A_fail[0]
        print('A counterexample: w1', r['w1'], 'w2', r['w2'], 'witness', r['A_witness'])


if __name__ == '__main__':
    main()
