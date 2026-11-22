"""Task 35: lemma:l_correc_properties (1) on the constructor-mode L-corrections (lcorr_constructor.py).
R^1(T^{L,+}(w)) ~ T^{L,-}(swapW w), R^2(T^{L,+}(w)) ~ T^{L,-}(w), R^3(T^{L,+}(w)) ~ T^{L,+}(swapW w); '~' up to translation.
A check is inconclusive when the odd partner has a pure-3 ancestor (the odd base-run case, where constructor-mode fails)."""
import sys
import lcorr_tex as L
import lcorr_constructor as K
import native_compare as nc
import alt_tiles as at

WORDS = ['1', '2', '3', '11', '12', '13', '21', '22', '23', '31', '32', '33',
         '111', '112', '113', '121', '122', '123', '131', '132', '133',
         '211', '212', '213', '221', '222', '223', '231', '232', '233',
         '311', '312', '313', '321', '322', '323', '331', '332', '333']


def main(path):
    P, _ = L.parse_lcorr(path)
    out = {'R1': [0, 0, 0], 'R2': [0, 0, 0], 'R3': [0, 0, 0]}   # checked, fail, inconclusive
    first = {'R1': [], 'R2': [], 'R3': []}
    for w in WORDS:
        u = w.rstrip('3')
        if not u or u[-1] not in '12' or len(u) > 2:
            continue
        sw = at.swapW(w)
        for elong in (True, False):
            Ep = nc.normalised(K.cand(P, 'even', w, False, elong))
            Em = nc.normalised(K.cand(P, 'even', w, True, elong))
            sw_u = sw.rstrip('2')
            base_partner = set(sw_u) == {'3'}
            ok_partner = bool(sw_u) and sw_u[-1] in '13' and len(sw_u) <= 2
            Op = nc.normalised(K.cand(P, 'odd', sw, False, elong)) if ok_partner else None
            Om = nc.normalised(K.cand(P, 'odd', sw, True, elong)) if ok_partner else None
            R1 = nc.normalised(at.rot(Ep)); R2 = nc.normalised(at.rot(at.rot(Ep))); R3 = nc.normalised(at.rot(at.rot(at.rot(Ep))))
            checks = [('R1', R1, Om), ('R2', R2, Em), ('R3', R3, Op)]
            for name, lhs, rhs in checks:
                tag = (w, 'long' if elong else 'short')
                if name != 'R2' and (base_partner or rhs is None):
                    out[name][2] += 1
                    continue
                out[name][0] += 1
                if lhs != rhs:
                    out[name][1] += 1
                    first[name].append(tag)
    for name in ('R1', 'R2', 'R3'):
        c, f, inc = out[name]
        print('%s: %d conclusive checks, %d fail (up to translation), %d inconclusive; first failing %s' %
              (name, c, f, inc, first[name][:4]))


if __name__ == '__main__':
    main(sys.argv[1])
