import sys
sys.path.insert(0, 'scripts')
from permit_local import standard, Frame, proper_words, h0
def run(w, B=None):
    F, _ = standard(w)
    fr = Frame(w)
    n, d, L, T = fr.n, fr.d, fr.L, fr.T
    if B is None:
        B = 2 * (n + d) + T
    ev_tot = ev_bad = 0
    od_tot = od_bad = 0
    ev_bad_pts = []
    od_bad_pts = []
    for x in range(-B, B + 1):
        for y in range(-B, B + 1):
            t = n * x - d * y
            s = L * x + (d - n) * y
            if (x + y) % 2 == 0 and 2 - L <= t <= 2 * L - 2:
                ev_tot += 1
                if F((x, y)) != 0:
                    ev_bad += 1
                    if len(ev_bad_pts) < 3: ev_bad_pts.append(((x, y), t, s, F((x, y))))
            if (x + y) % 2 == 1 and 2 - 3 * d + n <= s <= 3 * d + n - 2:
                od_tot += 1
                if F((x, y)) != h0(x, y):
                    od_bad += 1
                    if len(od_bad_pts) < 3: od_bad_pts.append(((x, y), t, s, F((x, y)), h0(x, y)))
    return dict(word=''.join(map(str, w)), n=n, d=d, L=L, T=T, even_zero_pts=ev_tot, even_bad=ev_bad,
                odd_h0_pts=od_tot, odd_bad=od_bad, ev_bad_ex=ev_bad_pts, od_bad_ex=od_bad_pts)
if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    for w in proper_words(maxlen):
        if all(x == 2 for x in w):
            continue
        print(run(w), flush=True)
