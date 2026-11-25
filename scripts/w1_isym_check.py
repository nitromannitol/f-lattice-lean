import sys
sys.path.insert(0, 'scripts')
from permit_local import standard, Frame
for w in [(1,), (1, 2)]:
    F, _ = standard(w)
    fr = Frame(w)
    B = 2 * (fr.n + fr.d) + fr.T
    bad = tot = 0
    ex = []
    for x in range(-B, B + 1):
        for y in range(-B, B + 1):
            tot += 1
            if F((1 - x, -1 - y)) != F((x, y)):
                bad += 1
                if len(ex) < 3:
                    ex.append(((x, y), fr.t((x, y)), F((x, y)), F((1 - x, -1 - y))))
    print(w, 'global I-symmetry: points', tot, 'mismatches', bad, 'examples', ex)
