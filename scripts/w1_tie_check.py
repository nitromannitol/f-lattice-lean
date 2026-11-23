#!/usr/bin/env python3
"""Numerical check of the tie band facts used by the hagree closure (task 84), on proper words of length <= 3.

For a word w (the current word) with earlier word u = conjWord w = swap(oddBirthPrefix w):
  G = standard(u)  (the earlier field, periodized);  lv = sheetShift(w);  A, C, M = sheetA, sheetC, sheetMin (permit_local.standard);
  psi(c) = C(c) - A(c);  parent z = zTurn(c - lv) = (-(c2 - lv2), c1 - lv1 - 1).
Free roots: the H and V trace points of the frame of u (w1_free_table_check.base_traces) that are white for G.
Sheet point of a free root z: c = zTurnInv(z) + lv, zTurnInv(q) = (q2 + 1, -q1).

Questions (answers feed the closure of the tie band under the return chains):
 Q1  is the sheet laplacian lap A(c) equal to lap G(z) at the sheet point of a free root?
 Q2  is every free white TIE root M-white (lap M(c) = 0)?
 Q3  for free white tie roots, are both sheet inputs of c ties (psi = 0)?
 Q4  is the tie set {psi = 0} the level set {Phi = K} of the chain potential (Phi = C - A + const along the sheet)?
"""
import sys
from collections import Counter

import permit_local as P
import w1_free_table_check as F


def sheet_fields(w):
    """A, C, M of the word w, as in permit_local.standard, and the sheet shift lv."""
    conj = tuple(P.swap(P.odd_birth_prefix(list(w))))
    G, _ = P.standard(conj)
    Fp = lambda x: G((-x[1], x[0] - 1)) + P.h0(*x)
    fr = P.Frame(list(w))
    eps = fr.eps
    W = (1 + eps) // 2
    dq, nq = fr.dq, fr.nq
    Uq = (dq, nq)
    Vq = (nq - dq, dq + nq)
    lv = ((1 - W) * Uq[0], (1 - W) * Uq[1])
    e = (Vq[0] + eps * Uq[0], Vq[1] + eps * Uq[1])
    Tq = dq * dq + 2 * dq * nq - nq * nq
    ce = (Tq - dq - nq) // 2 + 2 * W
    A = lambda z: Fp((z[0] - lv[0], z[1] - lv[1]))
    C = lambda z: (Fp((z[0] - lv[0] - e[0], z[1] - lv[1] - e[1])) + nq * (z[0] - lv[0]) - dq * (z[1] - lv[1]) + ce)
    M = lambda z: min(A(z), C(z))
    return G, A, C, M, lv


def run(maxlen=3):
    stats = Counter()
    examples = []
    words = [()] + list(P.proper_words(maxlen))
    for w in words:
        G, A, C, M, lv = sheet_fields(w)
        conj = tuple(P.swap(P.odd_birth_prefix(list(w))))
        fc = P.Frame(list(conj))
        H, V = F.base_traces(fc)
        roots = sorted(set(H) | set(V))
        for z in roots:
            lapG = P.lap(G, z)
            if lapG != 0:
                stats["free_black_root"] += 1
                continue
            stats["free_white_root"] += 1
            # sheet point of the root
            c = (z[1] + 1 + lv[0], -z[0] + lv[1])
            back = (-(c[1] - lv[1]), c[0] - lv[0] - 1)
            assert back == z, (w, z, c, back)
            psi = C(c) - A(c)
            lapA, lapC, lapM = P.lap(A, c), P.lap(C, c), P.lap(M, c)
            stats["q1_lapA_eq_lapG"] += int(lapA == lapG)
            stats["q1_total"] += 1
            if psi == 0:
                stats["tie_free_white"] += 1
                stats["tie_lapM_%d" % lapM] += 1
                ins = P.neighbours(c)
                tie_in = [C(i) - A(i) == 0 for i in ins]
                stats["tie_inputs_both_tie"] += int(all(tie_in))
                stats["tie_inputs_count_%d" % sum(tie_in)] += 1
                if lapM != 0 and len(examples) < 6:
                    examples.append((w, z, c, lapM, lapA, lapC, tie_in))
            else:
                stats["nontie_free_white"] += 1
    print("proper words + empty word, length <= %d: %d words" % (maxlen, len(words)))
    for k in sorted(stats):
        print(k, stats[k])
    print("examples of free white ties that are NOT M-white (w, z, c, lapM, lapA, lapC, input ties):")
    for ex in examples:
        print("  ", ex)


if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
