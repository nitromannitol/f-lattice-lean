import itertools
import permit_local as pl

def check(w, R=None):
    Fp, Xi, off = pl.model(w)
    fr = pl.Frame(list(w))
    R = R or (2 * fr.d + 4)
    false_A = false_C = 0
    unit_bad = 0
    pairs = 0
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            c = (x, y)
            for i in pl.neighbours(c):
                pairs += 1
                if not (Xi(i) <= Xi(c)): false_A += 1
                ci = (c[0] + off[0], c[1] + off[1]); ii = (i[0] + off[0], i[1] + off[1])
                if not (Xi(ci) <= Xi(ii)): false_C += 1
                dd = Xi(i) - Xi(c)
                if not (-1 <= dd <= 1): unit_bad += 1
    # deck invariance under the odd parent f = parents(w)[0]: K = mu*(D,N), V = (N-D, N+D)
    (N, D), _ = pl.parents(list(w))
    mu = 1 if (N + D) % 2 == 0 else 2
    K = (mu * D, mu * N); V = (N - D, N + D)
    inv_bad = {}
    for name, v in (("K", K), ("V", V)):
        diffs = set()
        for x in range(-R, R + 1, 2):
            for y in range(-R, R + 1, 3):
                z = (x, y)
                zv = (x + v[0], y + v[1])
                diffs.add(Xi(zv) - Xi(z))
        inv_bad[name] = len(diffs)
    return pairs, false_A, false_C, unit_bad, inv_bad, (K, V)

words = [w for L in range(1, 4) for w in itertools.product((1, 2, 3), repeat=L) if any(x != 3 for x in w)]
tot = [0, 0, 0, 0]
bad_inv = []
for w in words:
    pairs, fA, fC, ub, inv, KV = check(w)
    tot[0] += pairs; tot[1] += fA; tot[2] += fC; tot[3] += ub
    if inv["K"] != 1 or inv["V"] != 1:
        bad_inv.append((w, inv, KV))
print("words", len(words), "edge pairs", tot[0], "permitA false", tot[1], "permitC false", tot[2], "unit-increment violations", tot[3])
print("deck-invariance failures (number of distinct shifts > 1):", len(bad_inv))
for b in bad_inv[:5]:
    print("  ", b)
