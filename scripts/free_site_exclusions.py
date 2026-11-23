"""Task 72 (Q1 paragraph 6, the ordered free-site removals): numeric survey of the '+' row.

Q1.md l.21-28: with L = d + n and r = D + N, the '+' row lists the free sites in the order
  V_{-r-1}, ..., V_{-1},  H_0, V_0, V_1, ..., V_{L-r-2},  H_{d-1}-U, ..., H_1-U,
with V_{j+L} = V_j + V.  Here H_j = H[j] and V_j = V[j] are the free H and V sites of the child (curves of `routes.py`,
FIXED_FREE_GAME_AUDIT section 2), U = (d, n) (kernel), V = (n - d, n + d) (transverse).

Checks, for every odd coprime child n/d (d <= DMAX) and every r in [0, L-1]:
 (1) the free sites H[j], V[j] are the free sites of the Lean definitions (ChildFrame.freeH / freeV, S3FreeBoundary), in E;
 (2) the row has L + d entries in pairwise distinct deck classes (exact class key below), so it lists every free class once;
 (3) every consecutive pair inside the V block (ascending) and inside the H block (descending, reversed) is a short passage of the
     route classes of FIXED_FREE_GAME_AUDIT sections 3-4 (E, E-N, N-E-S on H; N, N-W, W-N-E on V), and its interior sites are
     nonfree (no deck translate on the free H/V set);
 (4) the transitions (V_{-1}, H_0), (H_0, V_0), (V_{L-r-2}, H_{d-1}-U), (H_1-U, V_{-r-1}) are counted as TIP routes (TIP_THEOREM).
"""
import math, sys

def curves(n, d):
    def edges(a, b):
        bits = [b * (i + 1) // (a + b) - b * i // (a + b) for i in range(1, a + b - 1)]
        return [0] + [e for bit in bits for e in ([1] if bit else [0, 0])] + [0]
    H = [(1, 0)]
    V = [(0, 0)]
    for e in edges((d - n) // 2, n):
        H.append((H[-1][0] + 1, H[-1][1] + e))
    for e in edges(n, d - n):
        V.append((V[-1][0] - e, V[-1][1] + 1))
    return H, V

def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def mul(k, a): return (k * a[0], k * a[1])

def lean_free_sets(n, d):
    """Free H and V sets of the closed polygon, from the Lean definitions (S3FreeBoundary, Sheets, ChildFrame)."""
    T = d * d + 2 * d * n - n * n
    def even(z): return (z[0] + z[1]) % 2 == 0
    def t(z): return n * z[0] - d * z[1]
    def s(z): return (d + n) * z[0] + (d - n) * z[1]
    def inE(z):
        if even(z):
            return 2 - T <= t(z) <= d + n - 2 and 0 <= s(z) <= T + 2 * n
        return n - T <= t(z) <= d and 2 - d + n <= s(z) <= T + d + n - 2
    def hS(x): return (x % 2 == 0 and 2 <= x <= d + n - 2) or (x % 2 == 1 and n <= x <= d)
    def vS(x): return x % 2 == 0 and ((0 <= x <= 2 * n) or (2 - d + n <= x <= d + n - 2))
    return T, inE, (lambda z: inE(z) and not inE((z[0], z[1] - 1)) and hS(t(z))), \
        (lambda z: inE(z) and not inE((z[0] - 1, z[1])) and vS(s(z)))

def make_key(n, d):
    T = d * d + 2 * d * n - n * n
    K = (d, n)
    V = (n - d, n + d)
    def key(z):
        x, y = z
        return ((x * V[1] - y * V[0]) % T, (K[0] * y - K[1] * x) % T)
    return key

def main(dmax=31, check_all_r=True):
    total = dict(children=0, rows=0, entries=0, V_pairs=0, H_pairs=0, transitions=0, middles=0, bad_middles=0,
                 not_free=0, class_clash=0, lean_mismatch=0)
    failures = []
    for d in range(3, dmax + 1, 2):
        for n in range(1, d, 2):
            if math.gcd(n, d) != 1 or n + 2 > d:
                continue
            total['children'] += 1
            H, V = curves(n, d)
            T, inE, freeH, freeV = lean_free_sets(n, d)
            key = make_key(n, d)
            L = d + n
            # (1) the curves are the Lean free sets (base period)
            freeHs = {z for z in H}
            freeVs = {z for z in V}
            if not all(freeH(z) for z in H) or not all(freeV(z) for z in V):
                total['lean_mismatch'] += 1
                failures.append(('lean_mismatch', n, d))
            free_keys = {key(z): ('H', j) for j, z in enumerate(H)}
            free_keys.update({key(z): ('V', j) for j, z in enumerate(V)})
            if len(free_keys) != len(H) + len(V):
                total['class_clash'] += 1
                failures.append(('class_clash_base', n, d))
            U = (d, n)
            VV = (n - d, n + d)
            def Vj(j):
                q, k = divmod(j, L)
                return add(V[k], mul(q, VV))
            def Hj(j):
                q, k = divmod(j, d)
                return add(H[k], mul(q, U))
            for r in (range(0, L) if check_all_r else [0]):
                total['rows'] += 1
                row = []   # (label, site)
                for j in range(-r - 1, 0):             # V_{-r-1} .. V_{-1}
                    row.append(('V', j, Vj(j)))
                row.append(('H0', 0, Hj(0)))            # H_0
                for j in range(0, L - r - 1):           # V_0 .. V_{L-r-2}
                    row.append(('V', j, Vj(j)))
                for j in range(d - 1, 0, -1):           # H_{d-1}-U .. H_1-U
                    row.append(('Hd', j, sub(Hj(j), U)))
                # (2) entries pairwise in distinct deck classes, covering all free classes
                keys = [key(z) for _, _, z in row]
                total['entries'] += len(row)
                if len(set(keys)) != len(keys) or len(keys) != L + d:
                    total['class_clash'] += 1
                    failures.append(('row_classes', n, d, r))
                if set(keys) != set(free_keys.keys()):
                    total['class_clash'] += 1
                    failures.append(('row_cover', n, d, r))
                # (3) consecutive passages
                for a, b in zip(row, row[1:]):
                    la, ja, za = a
                    lb, jb, zb = b
                    if la == 'V' and lb == 'V':
                        total['V_pairs'] += 1
                        step = sub(zb, za)
                        # route rule of routes.py (ascending V)
                        if sum(za) % 2:
                            moves = [(0, 1)] if step == (0, 1) else [(0, 1), (-1, 0)]
                        else:
                            moves = [(-1, 0), (0, 1), (1, 0)]
                    elif la == 'Hd' and lb == 'Hd':
                        total['H_pairs'] += 1
                        # descending H pair: the forward route from zb to za, reversed
                        lo, hi = (zb, za)
                        step = sub(hi, lo)
                        if sum(lo) % 2 == 0:
                            moves = [(1, 0)] if step == (1, 0) else [(1, 0), (0, 1)]
                        else:
                            moves = [(0, 1), (1, 0), (0, -1)]
                        # the forward route visits the same interior sites as its reverse
                        path = [lo]
                        for e in moves:
                            path.append(add(path[-1], e))
                        assert path[-1] == hi, (n, d, r, lo, hi, moves)
                        for u in path[1:-1]:
                            total['middles'] += 1
                            if key(u) in free_keys:
                                total['bad_middles'] += 1
                                failures.append(('H_middle_free', n, d, r, u))
                        continue
                    else:
                        total['transitions'] += 1
                        continue
                    path = [za]
                    for e in moves:
                        path.append(add(path[-1], e))
                    if path[-1] != zb:
                        total['bad_middles'] += 1
                        failures.append(('V_route_end', n, d, r, za, zb))
                        continue
                    for u in path[1:-1]:
                        total['middles'] += 1
                        if key(u) in free_keys:
                            total['bad_middles'] += 1
                            failures.append(('V_middle_free', n, d, r, u))
    return total, failures

if __name__ == "__main__":
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 31
    total, failures = main(dmax)
    for k, v in total.items():
        print(f"{k}: {v}")
    print("failures:", len(failures), failures[:5])
