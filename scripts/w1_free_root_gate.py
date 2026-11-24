"""Free-root gate of Q_minus (task 118, W1 base, step (ii)).
For every native free point p and its prescribed direction e (free-root edge), the target t = p + e: the claim is that every
rank r of t (any alias translate of t that is a representative) satisfies r < rank(p). Checked for odd d = 3..15 with the
exact definitions (rep, valMinus, last-alias rank) of the replay."""
import importlib.util
spec = importlib.util.spec_from_file_location('f', 'scripts/w1_pure3_families.py')
f = importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
ALIASES = [(i, j) for i in range(-2, 3) for j in (-1, 0, 1)]

def shift(d, X, Y, i, j):
    return (X + i * d + j * (1 - d), Y + i + j * (d + 1))

def native(d, X, Y):
    return (2 - d <= X <= d and 0 <= Y <= d + 1 and 1 <= X + Y <= d + 2) or (X, Y) in [(0, 0), (2, d + 1)]

def isrep(d, X, Y):
    if f.isfree(d, X, Y): return True
    if not native(d, X, Y): return False
    for i, j in ALIASES:
        a, b = shift(d, X, Y, i, j)
        if f.isfree(d, a, b): return False
        if native(d, a, b) and (a > X or (a == X and b > Y)): return False
    return True

def ranks(d, X, Y):
    """All ranks of (X,Y): one per alias translate that is a representative."""
    out = []
    for i, j in ALIASES:
        a, b = shift(d, X, Y, i, j)
        if isrep(d, a, b):
            out.append((i, j, f.valMinus(d, a, b) - i * 2 * d + j * 2 * (d + 1)))
    return out

def prescribed(d, X, Y):
    if (X + Y) % 2 == 0: return (-1, 0)
    if f.isfree(d, X, Y) and Y == 0 and 1 <= X <= d: return (0, 1) if X == d else (0, -1)
    return (0, 1)

if __name__ == '__main__':
    for d in range(3, 16, 2):
        bad = []; nonnat = []; multi = []; cnt = 0
        for X in range(2 - d, d + 1):
            for Y in range(0, d + 2):
                if not native(d, X, Y) or not f.isfree(d, X, Y): continue
                cnt += 1
                dx, dy = prescribed(d, X, Y)
                tx, ty = X + dx, Y + dy
                if not native(d, tx, ty): nonnat.append(((X, Y), (tx, ty)))
                rk = ranks(d, X, Y)
                rp = [r for _, _, r in rk]
                if len(set(rp)) != 1: multi.append(((X, Y), rk))
                rt = [r for _, _, r in ranks(d, tx, ty)]
                if any(r >= min(rp) for r in rt): bad.append(((X, Y), (tx, ty), rt, rp))
        print('d=%d free roots %d nonnative-targets %d multi-rank-roots %d drop-violations %d' % (d, cnt, len(nonnat), len(multi), len(bad)), nonnat[:2], bad[:2])
