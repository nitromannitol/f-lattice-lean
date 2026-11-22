import itertools, permit_local as pl
from collections import Counter
c = Counter(); bad = []
for L in range(1, 9):
    for w in itertools.product([1, 2, 3], repeat=L):
        if all(x == 3 for x in w):
            continue
        try:
            f = pl.Frame(list(w))
        except Exception:
            continue
        c[f.n] += 1
        if f.n < 3:
            bad.append(w)
print("proper words checked up to length 8:", sum(c.values()), "numerators:", sorted(c)[:6], "bad:", bad[:5], flush=True)
