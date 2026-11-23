import sys, itertools
sys.path.insert(0, '/Users/ahmedbou-rabee/lean-work/flattice-wt/w1/scripts')
from permit_local import standard, Frame, proper_words, win, neighbours, lap

def add(z, v): return (z[0] + v[0], z[1] + v[1])

def interior(fr):
    # the grades (t, s) determine (x, y) through the matrix [[n, -d], [L, d - n]] of determinant T
    T, n, d, L = fr.T, fr.n, fr.d, fr.L
    out = set()
    # enumerate over the strict rectangle in (t, s) directly
    for t in range(-T - 2 * (n + d) - 4, T + 2 * (n + d) + 5):
        for s_ in range(-2 * (n + d) - 4, 2 * T + 2 * (n + d) + 5):
            num_x = (d - n) * t + d * s_
            num_y = -L * t + n * s_
            if num_x % T or num_y % T:
                continue
            x, y = num_x // T, num_y // T
            a, b, c, h = win((x + y) % 2 == 0, n, d)
            if b - T < t < a and h < s_ < T + c:
                out.add((x, y))
    return out

def run(w):
    F, _ = standard(w)
    fr = Frame(w)
    inter = interior(fr)
    assert len(inter) == fr.T - fr.d - fr.L, (w, len(inter), fr.T - fr.d - fr.L)
    binary = all(lap(F, z) in (-1, 0) for z in inter)
    black = {z for z in inter if lap(F, z) == -1}
    white = {z for z in inter if lap(F, z) == 0}
    # unit squares with all four corners strictly interior
    squares = []
    for (a, b) in inter:
        S = [(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)]
        if all(c in inter for c in S):
            squares.append(S)
    def inside_input(c, S):
        ins = [i for i in neighbours(c) if i in S]
        assert len(ins) == 1, (c, S, ins)
        return ins[0]
    # unseeded unit propagation: forced[c] = outside input chosen by a square rule
    forced = {}
    conflict = 0
    changed = True
    while changed:
        changed = False
        for S in squares:
            wh = [c for c in S if c in white]
            if len(wh) != 1 and not (len(wh) > 1):
                pass
            for c in wh:
                others = [p for p in S if p != c]
                ok = True
                for p in others:
                    if p in black:
                        continue
                    if p in forced and forced[p] == inside_input(p, S):
                        continue
                    ok = False
                    break
                if ok:
                    o = [i for i in neighbours(c) if i not in S][0]
                    if c in forced and forced[c] != o:
                        conflict += 1
                    elif c not in forced:
                        forced[c] = o
                        changed = True
    forced_set = set(forced)
    # induced graph on the strictly interior sites: black keeps both inputs, forced white keeps its forced input
    nodes = black | forced_set
    edges = {}
    for z in nodes:
        if z in black:
            targets = [i for i in neighbours(z) if i in inter]
        else:
            targets = [forced[z]] if forced[z] in inter else []
        edges[z] = targets
    # cycle detection (DFS)
    state = {}
    cyc = False
    sys.setrecursionlimit(100000)
    def dfs(u):
        nonlocal cyc
        state[u] = 1
        for v in edges.get(u, []):
            if v not in nodes:
                continue
            if state.get(v) == 1:
                cyc = True
            elif state.get(v) is None:
                dfs(v)
        state[u] = 2
    for u in nodes:
        if state.get(u) is None:
            dfs(u)
    return dict(word=''.join(map(str, w)), T=fr.T, interior=len(inter), black=len(black), white=len(white),
                forced=len(forced_set), missed=len(white - forced_set), conflicts=conflict,
                binary=binary, dag=not cyc, squares=len(squares))

if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    rows = []
    for w in proper_words(maxlen):
        if all(x == 2 for x in w):
            continue
        rows.append(run(w))
    for r in rows:
        print(r)
    print('words', len(rows))
    print('all binary', all(r['binary'] for r in rows))
    print('all white forced (missed=0)', all(r['missed'] == 0 for r in rows))
    print('all dag', all(r['dag'] for r in rows))
    print('conflicts total', sum(r['conflicts'] for r in rows))
