"""Restricted escape (restricted burning) on the deck quotient, for the three permit systems of the restricted-fort
conditions, on every proper word of length <= 4.

Lean definitions followed:
  RestrictedEscapesWithin field grade permits level: a site escapes if grade < level, or if its laplacian is -1 and both
  inputs are permitted and escape, or its laplacian is 0 and one permitted input escapes (RestrictedBellmanRank.lean).
  RestrictedNoFort: no nonempty fort in a grade half-space, where a fort is a set each of whose sites is blocked by an
  input in the set or not permitted (RankFromForts.lean).
  Systems:
    S3: field F = standardField word, permits c i := slipIncrement F (F(.+sigma)) c i <= 0 (slipPermits),
        deck = the child's modified deck (kernel mu(d,n), transverse (n-d, n+d)), grade = frame.tGrade.
    I3A: field Fp = quarterTurnField G, permits c i := Xi i <= Xi c, deck = odd parent's modified deck.
    I3C: field Fp, permits c i := Xi (c + e) <= Xi (i + e), same deck, grade = frame.tGrade.
  Cover: one site per class, {z : kernelNumerator z, transverseNumerator z in [0, det)} (size det).

Method. For a cover site s with level L = grade s, escape is computed as a fixpoint on the window W around s (radius R),
where a site outside W escapes exactly when grade < L (pessimistic about the outside). Any escape found is a true
escape. If every cover site escapes, the finite-quotient criterion gives RestrictedNoFort. A nonempty set of unescaped
sites in W that is closed under blocking (each site blocked by an unescaped site of the set, or not permitted, and no
input outside W is unescaped) is a genuine finite fort, which would refute RestrictedNoFort.
"""
import sys
from collections import deque

import permit_local as pl


def neighbours(x):
    return pl.neighbours(x)


def cover_sites(K, V):
    """The sites z with kernelNumerator(z) = V.2 z1 - V.1 z2 and transverseNumerator(z) = K.1 z2 - K.2 z1 in [0, det)."""
    det = K[0] * V[1] - K[1] * V[0]
    delta = V[1] * K[0] - V[0] * K[1]          # det of the numerator map, +-det
    assert abs(delta) == abs(det)
    out = []
    for kn in range(abs(det)):
        for tn in range(abs(det)):
            # solve (V.2 z1 - V.1 z2, K.1 z2 - K.2 z1) = (kn, tn)
            a11, a12 = V[1], -V[0]
            a21, a22 = -K[1], K[0]
            dA = a11 * a22 - a12 * a21
            z1n = a22 * kn - a12 * tn
            z2n = -a21 * kn + a11 * tn
            if z1n % dA == 0 and z2n % dA == 0:
                out.append((z1n // dA, z2n // dA))
    return det, out


def escape_fixpoint(center, R, lap, perm, grade, L):
    """Return (escaped set inside the window, window set)."""
    cx, cy = center
    W = [(x, y) for x in range(cx - R, cx + R + 1) for y in range(cy - R, cy + R + 1)]
    inW = set(W)
    esc = {z for z in W if grade(z) < L}

    def is_esc(z):
        return (z in esc) if z in inW else (grade(z) < L)

    queue = deque(z for z in W if z not in esc)
    while queue:
        z = queue.popleft()
        if z in esc:
            continue
        a, b = neighbours(z)
        l = lap(z)
        pa, pb = perm(z, a), perm(z, b)
        ea, eb = is_esc(a), is_esc(b)
        ok = (l == -1 and pa and pb and ea and eb) or (l == 0 and ((pa and ea) or (pb and eb)))
        if ok:
            esc.add(z)
            for w in ((z[0] + 1, z[1]), (z[0] - 1, z[1]), (z[0], z[1] + 1), (z[0], z[1] - 1)):
                if w in inW and w not in esc:
                    queue.append(w)
    return esc, W


def is_genuine_fort(U, lap, perm, grade, L):
    """U: unescaped sites in the window. Genuine if each site is blocked by an input in U or not permitted."""
    for u in U:
        if grade(u) < L:
            return False
        a, b = neighbours(u)
        l = lap(u)
        ba = (a in U) or (not perm(u, a))
        bb = (b in U) or (not perm(u, b))
        if l == -1:
            if not ((ba) or (bb)):
                return False
        elif l == 0:
            if not (ba and bb):
                return False
        else:
            return False
    return True


def systems_for(word):
    """Return a dict name -> (lap, perm, grade, K, V, tag) for the three systems of a proper word."""
    w = list(word)
    fr = pl.Frame(w)
    N, D = pl.parents(w)[0]
    n, d = fr.n, fr.d
    grade = lambda z: n * z[0] - d * z[1]
    # child deck (even child): mu = 1
    mu_c = 1 if (n + d) % 2 == 0 else 2
    Kc = (mu_c * d, mu_c * n)
    Vc = (n - d, n + d)
    # odd parent deck
    mu_o = 1 if (N + D) % 2 == 0 else 2
    Ko = (mu_o * D, mu_o * N)
    Vo = (N - D, N + D)
    out = {}
    # S3
    F, _ = pl.standard(tuple(w))
    sig = (2 * fr.eps * D, 2 * fr.eps * N)
    slip = lambda c, i: (F(i) - F((i[0] + sig[0], i[1] + sig[1]))) - (F(c) - F((c[0] + sig[0], c[1] + sig[1])))
    out["S3"] = (lambda z: pl.lap(F, z), lambda c, i: slip(c, i) <= 0, grade, Kc, Vc)
    # I3 systems
    Fp, Xi, off = pl.model(w)
    permA = lambda c, i: Xi(i) <= Xi(c)
    permC = lambda c, i: Xi((c[0] + off[0], c[1] + off[1])) <= Xi((i[0] + off[0], i[1] + off[1]))
    out["I3A"] = (lambda z: pl.lap(Fp, z), permA, grade, Ko, Vo)
    out["I3C"] = (lambda z: pl.lap(Fp, z), permC, grade, Ko, Vo)
    return out, fr


def run_word(word, radii=(8, 14)):
    systems, fr = systems_for(word)
    res = {}
    for name, (lap, perm, grade, K, V) in systems.items():
        det, S0 = cover_sites(K, V)
        row = {"det": det, "cover": len(S0), "fail8": [], "fail14": [], "forts": 0,
               "min_unesc8": None, "min_unesc14": None, "binary_ok": True}
        # binary Laplacian check on the cover window
        for z in S0:
            if lap(z) not in (-1, 0):
                row["binary_ok"] = False
        for s in S0:
            L = grade(s)
            esc, W = escape_fixpoint(s, radii[0], lap, perm, grade, L)
            if s not in esc:
                U = set(W) - esc
                row["fail8"].append(s)
                row["min_unesc8"] = len(U) if row["min_unesc8"] is None else min(row["min_unesc8"], len(U))
                # genuine finite fort test on the unescaped part (sites in U blocked within U)
                U_grade = {u for u in U if grade(u) >= L}
                if U_grade and is_genuine_fort(U_grade, lap, perm, grade, L):
                    row["forts"] += 1
                esc2, W2 = escape_fixpoint(s, radii[1], lap, perm, grade, L)
                if s not in esc2:
                    row["fail14"].append(s)
                    U2 = set(W2) - esc2
                    row["min_unesc14"] = len(U2) if row["min_unesc14"] is None else min(row["min_unesc14"], len(U2))
                    U2g = {u for u in U2 if grade(u) >= L}
                    if U2g and is_genuine_fort(U2g, lap, perm, grade, L):
                        row["forts"] += 1
        res[name] = row
    return res


def proper_words(maxlen):
    import itertools
    for Lw in range(1, maxlen + 1):
        for w in itertools.product((1, 2, 3), repeat=Lw):
            if any(x != 3 for x in w):
                yield w


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    totals = {}
    words = list(proper_words(maxlen))
    print("proper words:", len(words), flush=True)
    for w in words:
        r = run_word(w)
        for name, row in r.items():
            t = totals.setdefault(name, {"words": 0, "cover_sites": 0, "escape_fail8": 0, "fail14": 0,
                                         "forts": 0, "all_burn_words": 0, "binary_bad": 0, "det_sum": 0,
                                         "cover_mismatch": 0})
            t["words"] += 1
            t["cover_sites"] += row["cover"]
            t["det_sum"] += row["det"]
            t["escape_fail8"] += len(row["fail8"])
            t["fail14"] += len(row["fail14"])
            t["forts"] += row["forts"]
            t["cover_mismatch"] += (row["cover"] != row["det"])
            t["all_burn_words"] += (len(row["fail8"]) == 0)
            t["binary_bad"] += (not row["binary_ok"])
            if row["fail14"] or row["forts"]:
                print("FAIL", name, w, "det", row["det"], "fail8", len(row["fail8"]), "fail14", len(row["fail14"]),
                      "forts", row["forts"], "min_unesc14", row["min_unesc14"], flush=True)
    for name, t in totals.items():
        print(name, t)
