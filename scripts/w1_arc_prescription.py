"""Exact-definition check (task 116, prescription field).

Sets follow the Lean definitions: closedPolygon (Sheets.lean, mem_closedPolygon_iff), freeH / freeV (S3FreeBoundary),
hSpectrum / vSpectrum, tGrade = n x - d y, sGrade = L x + (d-n) y, L = d+n, T = d^2 + 2dn - n^2 (child_facts).
Word child (n,d) = (2N+nq, 2D+dq) with odd = N/D, even = nq/dq, eps = N dq - nq D, W = (1+eps)/2,
lv = (1-W)(dq,nq). Conjugate child (nc,dc) = (D-N, D+N). zTurn x = (-x2, x1-1). Prescribed V direction (S3FreeBoundary):
vFirst -> (1,0); vLast -> (eta,0); even -> (eta,0); odd -> (0,-eta), with vLast = (nc-dc+1, nc+dc-1), vFirst = (0,0).
"""
import math
from collections import Counter

def even(p): return (p[0] + p[1]) % 2 == 0

class F:
    def __init__(self, n, d):
        self.n, self.d = n, d
        self.L = d + n
        self.T = d * d + 2 * d * n - n * n
    def t(self, z): return self.n * z[0] - self.d * z[1]
    def s(self, z): return self.L * z[0] + (self.d - self.n) * z[1]
    def cp(self, z):  # closedPolygon
        t, s = self.t(z), self.s(z)
        if even(z):
            return 2 - self.T <= t <= self.d + self.n - 2 and 0 <= s <= self.T + 2 * self.n
        return self.n - self.T <= t <= self.d and 2 - self.d + self.n <= s <= self.T + self.d + self.n - 2
    def hSpec(self, t):
        return (t % 2 == 0 and 2 <= t <= self.L - 2) or (t % 2 == 1 and self.n <= t <= self.d)
    def vSpec(self, s):
        return s % 2 == 0 and ((0 <= s <= 2 * self.n) or (2 - self.d + self.n <= s <= self.L - 2))
    def freeH(self, z):
        return self.cp(z) and not self.cp((z[0], z[1] - 1)) and self.hSpec(self.t(z))
    def freeV(self, z):
        return self.cp(z) and not self.cp((z[0] - 1, z[1])) and self.vSpec(self.s(z))
    def vLast(self): return (self.n - self.d + 1, self.n + self.d - 1)

def prescribedV(fr, eta, z):
    if z == (0, 0): return (1, 0)
    if z == fr.vLast(): return (eta, 0)
    if even(z): return (eta, 0)
    return (0, -eta)

def zTurn(x): return (-x[1], x[0] - 1)

def frames():
    for D in range(2, 16):
        for N in range(1, D):
            if math.gcd(N, D) != 1: continue
            for dq in range(1, 16):
                for nq in range(0, dq):
                    if math.gcd(nq, dq) != 1: continue
                    eps = N * dq - nq * D
                    if eps not in (1, -1): continue
                    n, d = 2 * N + nq, 2 * D + dq
                    if not (0 < n < d and d - n >= 2 and d >= 3 and (n + d) % 2 == 0): continue
                    nc, dc = D - N, D + N
                    if not (0 < nc < dc and dc - nc >= 2 and (nc + dc) % 2 == 0): continue
                    yield dict(N=N, D=D, nq=nq, dq=dq, eps=eps, n=n, d=d, nc=nc, dc=dc)

def windowed(fr, pred, xr, yr):
    return [(x, y) for x in range(*xr) for y in range(*yr) if pred((x, y))]

def check_sets(fr):
    """(A) H trace: one free H point per abscissa 1..d (and (1,0) free). (B) V cut: one free V point per ordinate 0..L-1."""
    okH = all(sum(1 for y in range(-3 * fr.L - 3 * fr.T - 5, 3 * fr.L + 3 * fr.T + 5) if fr.freeH((x, y))) == 1
              for x in range(1, fr.d + 1)) if False else None
    return None

def unique_by(fr, pred, key, rng_key, rng_lo, rng_hi, span):
    out = {}
    for k in rng_key(rng_lo, rng_hi):
        pts = [p for p in span(k) if pred(p)]
        if len(pts) != 1: return None
        out[k] = pts[0]
    return out

if __name__ == '__main__':
    stats = Counter()
    detail = []
    for c in frames():
        n, d, nc, dc, eps = c['n'], c['d'], c['nc'], c['dc'], c['eps']
        W = (1 + eps) // 2
        word, conj = F(n, d), F(nc, dc)
        stats['frames'] += 1
        # (A) free H trace: one point per abscissa 1..d
        Hpts = {}
        ok = True
        for x in range(1, d + 1):
            ys = [y for y in range(-3 * word.L - 3 * word.T - 5, 3 * word.L + 3 * word.T + 5) if word.freeH((x, y))]
            if len(ys) != 1: ok = False; break
            Hpts[x] = (x, ys[0])
        stats['H one per abscissa' if ok else 'H not one per abscissa'] += 1
        if not ok: continue
        # (B) free V cut: one point per ordinate 0..L_c-1
        Vpts = {}
        okV = True
        for y in range(0, conj.L):
            xs = [x for x in range(-3 * conj.L - 3 * conj.T - 5, 3 * conj.L + 3 * conj.T + 5) if conj.freeV((x, y))]
            if len(xs) != 1: okV = False; break
            Vpts[y] = (xs[0], y)
        stats['V one per ordinate' if okV else 'V not one per ordinate'] += 1
        if not okV: continue
        lv = (0, 0) if W == 1 else (c['dq'], c['nq'])
        if W == 0:
            pass
        # arc points in the sheet: W0 -> H_j ; W1 -> reflH(H_j) = (d+1-x, n-1-y)
        def arc(j):
            x, y = Hpts[j + 1]
            p = (x, y) if W == 0 else (d + 1 - x, n - 1 - y)
            return zTurn((p[0] - lv[0], p[1] - lv[1]))
        # each arc image should be a free V point of the conjugate
        imgs = [arc(j) for j in range(0, d)]
        onV = all(conj.freeV(a) for a in imgs)
        stats['W%d images on freeV' % W if onV else 'W%d images NOT on freeV' % W] += 1
        for eta in (1, -1):
            steps_ok = 0; steps_tot = 0
            for j in range(0, d - 1):
                a, b = imgs[j], imgs[j + 1]
                steps_tot += 1
                if (b[0] - a[0], b[1] - a[1]) == prescribedV(conj, eta, a): steps_ok += 1
            stats['W%d eta=%d steps=prescribed' % (W, eta)] += steps_ok
            stats['W%d eta=%d steps total' % (W, eta)] += steps_tot
        if len(detail) < 6 and not onV:
            detail.append((c, W, [imgs[j] for j in range(min(4, d))]))
    for k in sorted(stats): print(k, stats[k])
    for x in detail: print(x)
