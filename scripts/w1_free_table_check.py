#!/usr/bin/env python3
"""Policy-free check of the free-root return table (AUDIT_FREE_THREE_STEP_RETURNS sections 2-3) on proper words of length <= 4.

The canonical policy (the retained inputs of each white) is not reconstructed here, so the check covers exactly the content of the table
that does NOT depend on the policy's choices:

1. geometry: each row's four points form a unit square and the root z is its last point;
2. shape: each row matches one of the seven shapes S1..S7 of W1FreeSquare.lean, with the parity of z the shape requires;
3. vertices: each chain vertex (except z) is binary; a black vertex keeps both inputs (automatic); a free vertex is a named endpoint;
   a nonfree white vertex with exactly one free input must select it, so the table's next vertex must be that input (checked);
   a nonfree white vertex with no free input is a POLICY CHOICE (recorded, not checked);
4. fan rows: bulk rows whose first bulk edge comes from the forward or reflected fans (FIXED_FREE sections 8-9) are FLAGGED and named;
5. core sites: the audit's core black sites (1,1), (-1,0), (0,-2), (2,-1) are black; the bulk sites (2,1), (-1,1) if white have the
   free input the table uses ((2,0) and (0,1)).

Field and frame: permit_local.standard(u) is the earlier field G of word u (the conjugate of the current word), permit_local.Frame(u) its
child frame (n, d), T, U, V. Free sets follow S3FreeBoundary.lean (freeH, freeV, hSpectrum, vSpectrum) and closedPolygon (Sheets.lean);
`Nonfree` (NonfreeBridge.lean) is taken over deck translates i*U + j*V with |i|, |j| <= 3 (the free set is T-periodic in t and s).

Run from the scripts directory:  python3 w1_free_table_check.py [maxlen]
"""
import itertools
import sys
from collections import Counter

sys.setrecursionlimit(100000)

import permit_local as P  # noqa: E402  (standard field, frame, lap, neighbours, proper_words)


def closed(fr, z):
    """closedPolygon (Sheets.lean): the even and odd windows in the grades t = tGrade, s = sGrade."""
    t, s = fr.t(z), fr.sg(z)
    n, d, T = fr.n, fr.d, fr.T
    if (z[0] + z[1]) % 2 == 0:
        return 2 - T <= t <= d + n - 2 and 0 <= s <= T + 2 * n
    return n - T <= t <= d and 2 - d + n <= s <= T + d + n - 2


def hspec(fr, t):
    n, d = fr.n, fr.d
    return (t % 2 == 0 and 2 <= t <= d + n - 2) or (t % 2 == 1 and n <= t <= d)


def vspec(fr, s):
    n, d = fr.n, fr.d
    return s % 2 == 0 and ((0 <= s <= 2 * n) or (2 - d + n <= s <= d + n - 2))


def freeH(fr, z):
    return closed(fr, z) and not closed(fr, (z[0], z[1] - 1)) and hspec(fr, fr.t(z))


def freeV(fr, z):
    return closed(fr, z) and not closed(fr, (z[0] - 1, z[1])) and vspec(fr, fr.sg(z))


def translations(fr, K=3):
    n, d = fr.n, fr.d
    U = (d, n)
    V = (n - d, n + d)
    for i, j in itertools.product(range(-K, K + 1), repeat=2):
        yield (i * U[0] + j * V[0], i * U[1] + j * V[1])


def is_free(fr, z):
    """The site has a deck translate in freeH or freeV (negation of Nonfree)."""
    for v in translations(fr):
        w = (z[0] + v[0], z[1] + v[1])
        if freeH(fr, w) or freeV(fr, w):
            return True
    return False


def enumerate_points(fr, pred_t, pred_s, t_range, s_range):
    """All lattice points with t = n x1 - d x2 in t_range and s = L x1 + (d - n) x2 in s_range; det = T."""
    n, d, T = fr.n, fr.d, fr.T
    L = d + n
    for t in t_range:
        for s in s_range:
            x1n = (d - n) * t + d * s
            x2n = -L * t + n * s
            if x1n % T or x2n % T:
                continue
            x1, x2 = x1n // T, x2n // T
            assert n * x1 - d * x2 == t and L * x1 + (d - n) * x2 == s
            yield (x1, x2)


def base_traces(fr):
    n, d, T = fr.n, fr.d, fr.T
    L = d + n
    H = sorted({z for z in enumerate_points(fr, None, None, range(0, L + 1), range(-2 * L, T + 4 * L))
                if freeH(fr, z)})
    V = sorted({z for z in enumerate_points(fr, None, None, range(-T - 4 * L, L + 1), range(min(0, 2 - d + n) - 2, 2 * n + L + 1))
                if freeV(fr, z)}, key=lambda z: (z[1], z[0]))
    return H, V


def off(z, ds):
    return [(z[0] + a, z[1] + b) for a, b in ds]


SHAPES = {
    (((0, 1), (1, 1), (1, 0)), 1): "S1",
    (((1, 0), (1, 1), (0, 1)), 0): "S2",
    (((1, 0), (1, -1), (0, -1)), 0): "S3",
    (((0, -1), (1, -1), (1, 0)), 1): "S4",
    (((-1, 0), (-1, 1), (0, 1)), 0): "S5",
    (((0, 1), (-1, 1), (-1, 0)), 1): "S6",
    (((0, -1), (-1, -1), (-1, 0)), 1): "S7",
}


def rows_for(fr, H, V, eta):
    """The audit's row assignment (sections 2-3), with the same absolute paths. Yields (type, z, path, fan_flag)."""
    n, d = fr.n, fr.d
    U = (d, n)
    V0 = (n - d, n + d)
    out = []
    for i, z in enumerate(H):
        if i == 0:
            pp, typ, fan = [(1, 1), (2, 1), (2, 0), (1, 0)], "H0", False
        elif i == len(H) - 1:
            pp = off(U, [(0, 0), (1, 0), (1, -1), (0, -1)] if eta == -1 else [(0, -2), (1, -2), (1, -1), (0, -1)])
            typ, fan = "Hlast", False
        elif i == len(H) - 2:
            pp = off(U, [(0, -1), (0, -2), (-1, -2), (-1, -1)] if eta == -1 else [(0, -1), (0, 0), (-1, 0), (-1, -1)])
            typ, fan = "Hpenultimate", False
        elif (z[0] + z[1]) % 2:
            pp, typ, fan = off(z, [(0, 1), (1, 1), (1, 0), (0, 0)]), "Hmidpoint", True
        elif H[i + 1][1] > z[1]:
            pp, typ, fan = off(z, [(1, 0), (1, 1), (0, 1), (0, 0)]), "Hdiagonal", False
        else:
            pp, typ, fan = off(z, [(1, 0), (1, -1), (0, -1), (0, 0)]), "Haxial", True
        out.append((typ, z, pp, fan))
    for i, z in enumerate(V):
        if i == 0:
            pp = [(-1, 0), (-1, 1), (0, 1), (0, 0)] if eta == -1 else [(1, 0), (1, -1), (0, -1), (0, 0)]
            typ, fan = "V0", False
        elif i == len(V) - 1:
            pp, typ, fan = off(V0, [(2, -1), (2, 0), (1, 0), (1, -1)]), "Vlast", False
        elif i == 1 and eta == 1:
            pp, typ, fan = [(0, 0), (-1, 0), (-1, 1), (0, 1)], "Vfirst_odd", False
        elif i == len(V) - 2 and eta == -1:
            pp, typ, fan = off(V0, [(1, -1), (0, -1), (0, -2), (1, -2)]), "Vpenultimate", False
        elif (z[0] + z[1]) % 2 == 0:
            pp = off(z, [(-1, 0), (-1, 1), (0, 1), (0, 0)] if eta == -1 else [(1, 0), (1, -1), (0, -1), (0, 0)])
            typ, fan = "Vmidpoint", True
        elif eta == -1:
            if V[i + 1][0] < z[0]:
                pp, typ, fan = off(z, [(0, 1), (-1, 1), (-1, 0), (0, 0)]), "Vdiagonal", False
            else:
                pp, typ, fan = off(z, [(0, 1), (1, 1), (1, 0), (0, 0)]), "Vaxial", True
        else:
            if V[i - 1][0] > z[0]:
                pp, typ, fan = off(z, [(0, -1), (1, -1), (1, 0), (0, 0)]), "Vdiagonal", False
            else:
                pp, typ, fan = off(z, [(0, -1), (-1, -1), (-1, 0), (0, 0)]), "Vaxial", True
        out.append((typ, z, pp, fan))
    return out


def check_row(fr, F, typ, z, pp, fan, stats, notes):
    # 1. geometry: the four points are a unit square and z is the last point
    corners = set(pp)
    a = min(x for x, _ in corners)
    b = min(y for _, y in corners)
    square = {(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)}
    if pp[-1] != z or corners != square:
        stats["geometry_fail"] += 1
        notes.append(("geometry", typ, z))
        return
    stats["geometry_ok"] += 1
    # 2. shape
    rel = tuple((p[0] - z[0], p[1] - z[1]) for p in pp[:-1])
    par = (z[0] + z[1]) % 2
    shape = SHAPES.get((rel, par))
    if shape is None:
        stats["shape_fail"] += 1
        notes.append(("shape", typ, z, rel, par))
    else:
        stats["shape_" + shape] += 1
    # 3. vertices
    for k in range(len(pp) - 1):
        v, nxt = pp[k], pp[k + 1]
        lap = P.lap(F, v)
        if lap not in (-1, 0):
            stats["nonbinary"] += 1
            notes.append(("nonbinary", typ, v))
            continue
        if lap == -1:
            stats["black_vertex"] += 1
            continue
        if is_free(fr, v):
            stats["white_free_vertex"] += 1
            continue
        a_, b_ = P.neighbours(v)
        free_inputs = [w for w in (a_, b_) if is_free(fr, w)]
        if len(free_inputs) == 1:
            if free_inputs[0] == nxt:
                stats["white_nonfree_selects_free_ok"] += 1
            else:
                stats["white_nonfree_selection_mismatch"] += 1
                notes.append(("mismatch", typ, z, v, nxt, free_inputs[0]))
        elif len(free_inputs) == 0:
            stats["policy_choice_white"] += 1
            stats["policy_choice_row_" + typ] += 1
        else:
            stats["two_free_inputs"] += 1
            notes.append(("two_free", typ, z, v))
    if fan:
        stats["fan_row_flagged"] += 1


def core_checks(F, stats, notes, fr):
    for site in [(1, 1), (-1, 0), (0, -2), (2, -1)]:
        if P.lap(F, site) == -1:
            stats["core_black_ok"] += 1
        else:
            stats["core_black_fail"] += 1
            notes.append(("core", site, P.lap(F, site)))
    for site, need in [((2, 1), (2, 0)), ((-1, 1), (0, 1))]:
        if P.lap(F, site) == 0:
            a_, b_ = P.neighbours(site)
            if need in (a_, b_) and is_free(fr, need) and not is_free(fr, a_ if b_ == need else b_):
                stats["bulk_white_free_input_ok"] += 1
            else:
                stats["bulk_white_free_input_fail"] += 1
                notes.append(("bulk", site, need))


def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    words = [()] + list(P.proper_words(maxlen))
    total = Counter()
    per_word = []
    for u in words:
        F, _ = P.standard(tuple(u))
        fr = P.Frame(list(u))
        H, V = base_traces(fr)
        n, d = fr.n, fr.d
        ok_end = (H and H[0] == (1, 0) and H[-1] == (d, n - 1)) and (V and V[0] == (0, 0))
        if not ok_end:
            total["trace_endpoints_mismatch"] += 1
            per_word.append((u, "endpoints", H[:1], H[-1:], V[:1], V[-1:]))
        for eta in (-1, 1):
            stats = Counter()
            notes = []
            core_checks(F, stats, notes, fr) if eta == -1 else None
            for typ, z, pp, fan in rows_for(fr, H, V, eta):
                check_row(fr, F, typ, z, pp, fan, stats, notes)
                stats["rows_" + typ] += 1
            for k, v in stats.items():
                total[(eta, k)] += v
            if notes:
                per_word.append((u, eta, notes[:4]))
    print("proper words + empty word, length <= %d: %d words" % (maxlen, len(words)))
    for key in sorted(total, key=lambda x: str(x)):
        print(key, total[key])
    fails = [p for p in per_word if p[1] != "endpoints" and any(
        x[0] in ("geometry", "shape", "nonbinary", "mismatch", "two_free", "core", "bulk") for x in p[2])]
    print("words with failing checks:", len(fails))
    for item in fails[:12]:
        print("  ", item)


if __name__ == "__main__":
    main()
