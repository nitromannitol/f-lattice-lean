"""Task 72 (V-block converse, numerics): the odd conjugate free H points and V_p + I.

Conjugate child (n, d) = (D - N, D + N) of the word's odd parent N/D; word child (n_w, d_w) = the frame's own child.
Claims checked on words over {1,2,3} of length <= maxlen (default 4):
 (a) every odd free H point w of the conjugate has z = zTurn(w) = (-b, 2l - b) with b = w2, l = (w1 + w2 - 1)/2,
     and r = (D - N) l - D b satisfies 0 <= r <= N and b = floor((D - N) l / D) (direct from the H spectrum t = 2r + (D - N));
 (b) conversely every l in [0, D-1] with 0 <= r_l <= N is the image of exactly one odd conjugate free H point;
 (c) r_l = N holds exactly for l = D - 1, where z = (N - D + 1, N + D - 1) = excVertex = V_p + I;
 (d) the image z is in the word frame's freeV for every l with r_l <= N - 1 (in particular for l = 0, the origin);
 (e) the word child's index q = (d_w - n_w) l - d_w b satisfies q <= n_w whenever r_l <= N - 1 (1 <= l <= D - 1),
     which is the vSpectrum first branch needed in (d);
 (f) the excVertex is not in freeV for the words with eps = +1 (it is free for the others), so it is the only exception.
Usage: python3 scripts/conj_freeH_odd_check.py [maxlen]
"""
import os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conj_freeH_vpath_check import parents, Frame, even, freeH, freeV, box, zturn, words


def main(maxlen):
    c = Counter()
    for u in words(maxlen):
        (N, D), _ = parents(u)
        nc, dc = D - N, D + N
        fr = Frame(list(u))
        nw, dw = fr.n, fr.d
        exc = (N - D + 1, N + D - 1)
        imgs = Counter()
        for w in [z for z in box(nc, dc) if freeH(nc, dc, z)]:
            if even(w):
                continue
            c['odd_freeH'] += 1
            z = zturn(w)
            b = w[1]
            l2 = w[0] + w[1] - 1
            assert l2 % 2 == 0
            l = l2 // 2
            r = (D - N) * l - D * b
            ok = (0 <= l <= D - 1) and (0 <= r <= N) and b == (D - N) * l // D and z == (-b, 2 * l - b)
            c['(a)_ok' if ok else '(a)_BAD'] += 1
            imgs[l] += 1
            if r == N:
                c['(c)_r=N_is_exc' if (z == exc and l == D - 1) else '(c)_r=N_BAD'] += 1
            elif freeV(nw, dw, z):
                c['(d)_freeV' if r <= N - 1 else '(d)_freeV_at_r=N'] += 1
            else:
                c['(d)_NOT_freeV_r<N' if r <= N - 1 else '(d)_NOT_freeV_r=N'] += 1
        # (b): every l with 0 <= r_l <= N is hit exactly once
        for l in range(0, D):
            b = (D - N) * l // D
            r = (D - N) * l - D * b
            if 0 <= r <= N:
                c['(b)_hit_once' if imgs[l] == 1 else '(b)_MISS_or_multi'] += 1
            else:
                c['(b)_not_hit' if imgs[l] == 0 else '(b)_BAD_hit'] += 1
            # (e): word index q <= n_w for 1 <= l, r <= N-1
            if 1 <= l and r <= N - 1:
                q = (dw - nw) * l - dw * b
                c['(e)_q<=n' if q <= nw else '(e)_q>n_BAD'] += 1
        # (f): excVertex in freeV?
        c[('(f)_exc_free' if freeV(nw, dw, exc) else '(f)_exc_notfree', 'eps=+1' if fr.eps == 1 else 'eps=-1')] += 1
    return c


if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    res = main(maxlen)
    for k, v in sorted(res.items(), key=str):
        if v:
            print(v, k)
