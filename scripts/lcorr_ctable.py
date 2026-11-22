"""Task 35 diagnostic: replace single TeX table entries by the constructor's correctionJets values and recount."""
import sys
import lcorr_tex as L

ORIG_ODD = L.odd_table
ORIG_EVEN = L.even_table


def odd_ctable(case, p, q):
    K1, K2, K3, K4 = ORIG_ODD(case, p, q)
    vp1, vq1, vp2, vq2 = L.V1o(p), L.V1e(q), L.V2(p), L.V2(q)
    if case == '11':
        K1 = L.neg(vq2)                       # constructor: scan = -evenTrans
    if case == '00':
        K3 = L.add(L.neg(vq2), vp2)           # constructor: headStart = -evenTrans + oddTrans
    return K1, K2, K3, K4


def even_ctable(case, s, p, q):
    K1, K2, K3, K4 = ORIG_EVEN(case, s, p, q)
    vp1, vq1, vp2, vq2 = L.V1o(p), L.V1e(q), L.V2(p), L.V2(q)
    if case == '11':
        K2 = L.add(L.neg(vq1), L.neg(vq2), vp2)   # constructor: bridge = -evenKernel + oddTrans - evenTrans
    return K1, K2, K3, K4


def run(path, odd, even, label):
    L.odd_table = odd
    L.even_table = even
    P, C = L.parse_lcorr(path)
    res = L.compare(P, C, 'c')
    total = bad = 0
    print(label)
    for lab in sorted(res):
        rows = res[lab]
        fails = [r for r in rows if not r[3]]
        total += len(rows)
        bad += len(fails)
        print('  %-12s %2d checked, %2d differ' % (lab, len(rows), len(fails)))
    print('  total %d, differ %d' % (total, bad))


if __name__ == '__main__':
    path = sys.argv[1]
    run(path, ORIG_ODD, ORIG_EVEN, 'TeX tables (variant c)')
    run(path, odd_ctable, ORIG_EVEN, 'odd entries from constructor (K1 of 11, K3 of 00)')
    run(path, odd_ctable, even_ctable, 'plus even 11 K2 from constructor')
