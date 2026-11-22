"""Task 55 (R2), the run lemma: for a word u over {E,N,W} with no adjacent E,W pair, from the origin, with H = #N,
c = endpoint x, F(k) = column of the k-th north step (0 <= k < H), FF(-1) = 0, FF(k) = F(k) for 0 <= k < H, FF(H) = c:
  E-edge ((q,k),(q+1,k)) in walk  <->  0 <= k <= H and FF(k-1) <= q < FF(k)
  W-edge ((q+1,k),(q,k)) in walk  <->  0 <= k <= H and FF(k) <= q < FF(k-1)
  N-edge ((x,k),(x,k+1)) in walk  <->  0 <= k < H and x = F(k)
Checked on random words (lengths <= 9) over {E,N,W} without adjacent E,W.
Usage: python3 runlemma.py N"""
import sys, random
from collections import Counter

E, N, W = (1, 0), (0, 1), (-1, 0)
NAME = {E: "E", N: "N", W: "W"}


def walk(u):
    pts = [(0, 0)]; edges = []
    for d in u:
        nxt = (pts[-1][0] + d[0], pts[-1][1] + d[1])
        edges.append((pts[-1], nxt)); pts.append(nxt)
    return edges, pts


def check(u):
    edges, pts = walk(u)
    es = set(edges)
    H = sum(1 for d in u if d == N)
    c = sum(d[0] for d in u)
    F = {}
    x = 0; y = 0
    for d in u:
        if d == N: F[y] = x
        x += d[0]; y += d[1]
    def FF(j):
        if j < 0: return 0
        if j < H: return F[j]
        return c
    ok = True
    for k in range(-2, H + 3):
        for q in range(-12, 13):
            e_mem = ((q, k), (q + 1, k)) in es
            e_rhs = (0 <= k <= H and FF(k - 1) <= q < FF(k))
            w_mem = ((q + 1, k), (q, k)) in es
            w_rhs = (0 <= k <= H and FF(k) <= q < FF(k - 1))
            n_mem = ((q, k), (q, k + 1)) in es
            n_rhs = (0 <= k < H and q == F.get(k, 10**9))
            if e_mem != e_rhs or w_mem != w_rhs or n_mem != n_rhs: ok = False
    nodup = len(set(edges)) == len(edges)
    return ok, nodup

def noEW(u):
    return all(not ((u[j] == E and u[j+1] == W) or (u[j] == W and u[j+1] == E)) for j in range(len(u)-1))

if __name__ == "__main__":
    n = int(sys.argv[1])
    random.seed(3)
    cnt = Counter()
    for _ in range(n):
        L = random.randint(0, 9)
        u = [random.choice([E, N, W]) for _ in range(L)]
        if not noEW(u): cnt["skip"] += 1; continue
        ok, nodup = check(u)
        cnt[("formulas", ok)] += 1
        cnt[("nodup", nodup)] += 1
    print(dict(cnt))
