"""Task 43: a site-level Python port of the constructor (Construction/Native*.lean, CorrectionSchedule.lean, Offsets.lean).

Tiles are frozensets of sites. Every tile is kept up to translation: registers are lower-left normalised (llCenter) when
they are read (parentsFor, correctionPieces, correctionPair), as the Lean evaluator does, so the translations of outputs
never matter. Schedules are evaluated as the union of their placed copies, after the ordered contact check of
`PlacedSchedule.eval`; a failed contact raises `CtorError` (the Lean evaluator returns an error there).

Fractions are pairs (num, den), words are strings over '1', '2', '3'. The base-run registers are taken from the TeX
standard and alternate tiles (`alt_tiles`), as the lead's note says they agree with the base tiles; the validation
against the native logs for words of length at most three checks this.

Entry points:
  evaluate(word) -> State, the native state after the word (raises CtorError on an evaluator error);
  output(word) -> (odd, even, altOdd, altEven) the outputs of the word's last step (llCentered site sets).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import alt_tiles as at  # noqa: E402


class CtorError(Exception):
    pass


# ---------- tiles ----------

def shiftT(T, v):
    return frozenset((x + v[0], y + v[1]) for (x, y) in T)


def lowest(T):
    return min(T, key=lambda p: (p[1], p[0]))


def upper(T):
    return max(T, key=lambda p: (p[1], p[0]))


def llc(T):
    if not T:
        raise CtorError('empty tile')
    return shiftT(T, (-lowest(T)[0], -lowest(T)[1]))


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def neg(a):
    return (-a[0], -a[1])


def smul(k, a):
    return (k * a[0], k * a[1])


ZERO = (0, 0)


def kernelOff(f):
    """kernelJet: (den, num)."""
    return (f[1], f[0])


def transOff(f):
    """transverseJet: (num - den, num + den)."""
    return (f[0] - f[1], f[0] + f[1])


def evalPlaced(first, copies):
    """PlacedSchedule.eval: the first tile, then the copies in order; each copy must meet the occupied union."""
    occ = set(first)
    for c in copies:
        if not (occ & c):
            raise CtorError('disjoint required contact')
        occ |= c
    return frozenset(occ)


# ---------- jets (offsets only; slopes do not affect sites) ----------

def standardJetsOff(word, parity):
    P = at.parents_at(word)
    oK, oT = kernelOff(P[0]), transOff(P[0])
    eK, eT = kernelOff(P[1]), transOff(P[1])
    ph0 = at.phase(word) == 0
    if parity == 'odd':
        if ph0:
            # doubleFirst 0 (2oK+oT) (2eK) eT eK
            return [ZERO, eK, add(smul(2, oK), oT), add(add(smul(2, oK), oT), eK), smul(2, eK), eT]
        # doubleFirst (2oK) oT 0 (2eK+eT) eK
        return [smul(2, oK), add(smul(2, oK), eK), oT, add(oT, eK), ZERO, add(smul(2, eK), eT)]
    if ph0:
        # doubleLast 0 (2oK+2oT) eK eT oT
        return [ZERO, add(smul(2, oK), smul(2, oT)), eK, add(eK, oT), eT, add(eT, oT)]
    # doubleLast (2oK) (2oT) 0 (eT+eK) oT
    return [smul(2, oK), smul(2, oT), ZERO, oT, add(eT, eK), add(add(eT, eK), oT)]


def alternateJetsOff(word, parity):
    P = at.parents_at(word)
    oK, oT = kernelOff(P[0]), transOff(P[0])
    eK, eT = kernelOff(P[1]), transOff(P[1])
    ph0 = at.phase(word) == 0
    if parity == 'odd':
        if ph0:
            # doubleLast 0 (2oK+2oT+eK) eK eT (eK+oT)
            s = add(add(smul(2, oK), smul(2, oT)), eK)
            return [ZERO, s, eK, add(eK, add(eK, oT)), eT, add(eT, add(eK, oT))]
        # doubleLast (2oK) (2oT-eK) 0 (eK+eT) (-eK+oT)
        s = sub(smul(2, oT), eK)
        st = add(neg(eK), oT)
        return [smul(2, oK), s, ZERO, st, add(eK, eT), add(add(eK, eT), st)]
    if ph0:
        # doubleFirst 0 (2oK+oT) eK (oT-eK+eT) (-eK+oT)
        st = add(neg(eK), oT)
        return [ZERO, st, add(smul(2, oK), oT), add(add(smul(2, oK), oT), st), eK, add(add(oT, neg(eK)), eT)]
    # doubleFirst (2oK) oT 0 (oT+eT+2eK) (eK+oT)
    st = add(eK, oT)
    return [smul(2, oK), add(smul(2, oK), st), oT, add(oT, st), ZERO, add(add(oT, eT), smul(2, eK))]


def seventhOff(beforePush, digit, parity):
    word = beforePush + digit
    P = at.parents_at(word)
    oK, oT = kernelOff(P[0]), transOff(P[0])
    eK, eT = kernelOff(P[1]), transOff(P[1])
    ph0 = at.phase(word) == 0
    if parity == 'odd':
        if ph0:
            return add(eK, oT)
        if digit == '2':
            return oT
        return add(oT, sub(smul(2, oK), eK))
    if ph0:
        if digit == '1':
            return add(oT, sub(smul(2, oK), eK))
        if digit == '2':
            return eT
        return add(oT, sub(eK, smul(2, sub(eK, smul(2, oK)))))
    if digit == '2':
        return add(smul(2, eK), eT)
    return add(eK, oT)


def standardSources(parents, parity):
    E, O = parents['even'], parents['odd']
    if parity == 'odd':
        return [E, E, E, E, O, O]
    return [E, E, O, O, O, O]


AFTER_FIRST = {'odd': [1, 4, 5, 2, 3], 'even': [2, 3, 1, 4, 5]}
AFTER_SEVENTH = {'odd': [2, 3, 1, 4, 5], 'even': [1, 4, 2, 3, 5]}


def flip_parity(p):
    return 'even' if p == 'odd' else 'odd'


# ---------- the restorations and the birth of a retained fraction ----------

def retainedBirth(word, parity):
    """retainedBirth?: None at the endpoint of the root. Otherwise the birth prefix u = earlier, where word = earlier ++
    next :: rest and next is the last digit that updates the retained fraction of this parity (Parents.step: digits 1 and
    2 update the odd retained fraction, digits 1 and 3 the even one). Then Birth.fraction = current of u at the parity."""
    P = at.parents_at(word)
    f = P[0] if parity == 'odd' else P[1]
    rootf = (0, 1) if parity == 'odd' else (1, 1)
    if f == rootf:
        return None
    updates = ('1', '2') if parity == 'odd' else ('1', '3')
    for k in range(len(word) - 1, -1, -1):
        if word[k] in updates:
            u = word[:k]
            assert at.current(at.parents_at(u), parity) == f, (word, parity)
            return u
    raise CtorError('no birth for the retained fraction of %r' % word)


def alternateRestorationOff(word, parity):
    b = retainedBirth(word, parity)
    if b is None:
        return ZERO
    P = at.parents_at(b)
    offset = sub(kernelOff(P[1]), transOff(P[0]))
    if offset[1] < 0:
        return ZERO
    if parity == 'odd':
        return neg(offset) if at.phase(b) == 1 else ZERO
    if at.phase(b) == 0:
        extra = (0, 1) if all(d == '3' for d in b) else ZERO
        return neg(add(offset, extra))
    return ZERO


def restoreAlt(word, parity, T):
    return shiftT(T, alternateRestorationOff(word, parity))


# ---------- the ordinary schedules ----------

def ordinaryStandard(parents, word, parity):
    J = standardJetsOff(word, parity)
    S = standardSources(parents, parity)
    placed = [shiftT(S[i], J[i]) for i in range(6)]
    return evalPlaced(placed[0], [placed[i] for i in AFTER_FIRST[parity]])


def ordinaryAlternate(parents, beforePush, digit, parity):
    word = beforePush + digit
    J = alternateJetsOff(word, parity)
    S = standardSources(parents, flip_parity(parity))
    placed = [shiftT(S[i], J[i]) for i in range(6)]
    if parity == 'odd':
        oldAlt = restoreAlt(word, 'even', parents['alteven'])
    else:
        oldAlt = restoreAlt(word, 'odd', parents['altodd'])
    seventh = shiftT(oldAlt, seventhOff(beforePush, digit, parity))
    return evalPlaced(placed[0], [seventh] + [placed[i] for i in AFTER_SEVENTH[parity]])


# ---------- the corrections ----------

def align(parents, pair, beforePush, digit, standardParity):
    """alignCorrections: the helper aligned to the upper-right corner of the parent it replaces."""
    target = upper(parents['even'] if standardParity == 'odd' else parents['odd'])
    left, right = pair
    if digit != '3' and at.phase(beforePush + digit) == 1:
        R = shiftT(right, sub(target, upper(right)))
        return left, R
    L = shiftT(left, sub(target, upper(left)))
    return L, right


def correctedStandard(parents, pair, beforePush, digit, parity):
    word = beforePush + digit
    L, R = align(parents, pair, beforePush, digit, parity)
    E, O = parents['even'], parents['odd']
    if parity == 'odd':
        donors = [E, R, L, E, O, O] if at.phase(word) == 0 else [R, E, E, L, O, O]
    else:
        donors = [E, E, O, L, R, O]
    J = standardJetsOff(word, parity)
    placed = [shiftT(donors[i], J[i]) for i in range(6)]
    return evalPlaced(placed[0], [placed[i] for i in AFTER_FIRST[parity]])


def correctedAlternate(parents, pair, beforePush, digit, parity):
    word = beforePush + digit
    L, R = align(parents, pair, beforePush, digit, flip_parity(parity))
    E, O = parents['even'], parents['odd']
    if parity == 'odd':
        donors = [E, E, O, L, R, O]
    else:
        donors = [R, E, E, L, O, O]
    J = alternateJetsOff(word, parity)
    placed = [shiftT(donors[i], J[i]) for i in range(6)]
    return evalPlaced(placed[0], [placed[i] for i in [2, 3, 4, 5, 1]])


def correctionJetsOff(beforeLast, last, parity, flip):
    """(scan, bridge, headStart, headStep) offsets of correctionJets."""
    word = beforeLast + last
    P = at.parents_at(word)
    oK, oT = kernelOff(P[0]), transOff(P[0])
    eK, eT = kernelOff(P[1]), transOff(P[1])
    t = at.phase(word) == 1
    twiceOdd = smul(2, oK)
    if parity == 'odd':
        if t and not flip:
            return (eT, add(eT, sub(eK, twiceOdd)), add(add(neg(eT), oT), sub(twiceOdd, eK)), neg(eK))
        if not t and not flip:
            return (eT, eT, add(neg(eT), oT), eK)
        if t and flip:
            return (neg(eT), neg(oT), sub(twiceOdd, eK), eK)
        return (neg(eT), sub(neg(oT), sub(twiceOdd, eK)), ZERO, neg(eK))
    if t and not flip:
        hs = add(add(sub(eK, twiceOdd), sub(eT, oT)), eK) if last == '2' else sub(eK, twiceOdd)
        return (twiceOdd, twiceOdd, hs, oT)
    if not t and not flip:
        hs = sub(eT, oT) if last == '2' else sub(twiceOdd, eK)
        return (neg(twiceOdd), neg(eK), hs, oT)
    if t and flip:
        hs = add(sub(eT, oT), eK) if last == '2' else ZERO
        return (neg(twiceOdd), add(neg(eK), sub(oT, eT)), hs, neg(oT))
    hs = sub(sub(eT, oT), sub(twiceOdd, eK)) if last == '2' else ZERO
    return (twiceOdd, add(twiceOdd, sub(oT, eT)), hs, neg(oT))


def correctionPieces(saved, ancestorPrefix, last, beforePush, parity, flip, elongated, L):
    """correctionPieces: returns the first tile and the rest (copies), all as site sets."""
    ancestor = ancestorPrefix + last
    st = saved['st']
    al = saved['al']
    if parity == 'odd':
        stem, cross = st['re'], st['ro']
        head = restoreAlt(beforePush, 'even', al['re'])
    else:
        stem, cross = st['ro'], st['re']
        head = restoreAlt(beforePush, 'odd', al['ro'])
    scan, bridge, hS, hStep = correctionJetsOff(ancestorPrefix, last, parity, flip)
    start = standardJetsOff(beforePush, parity)[3 if parity == 'odd' else 5] if flip else ZERO
    bridgeJet = add(add(start, smul(L, scan)), bridge)
    bridgeTile = shiftT(cross, bridgeJet)
    if parity == 'odd' and all(d == '3' for d in ancestor):
        bridgeTile = shiftT(bridgeTile, (1, -1) if flip else (0, -1))
    elif parity == 'even' and flip and all(d == '2' for d in ancestor):
        bridgeTile = shiftT(bridgeTile, (1, 1))
    first = shiftT(stem, start)
    scanCopies = [shiftT(stem, add(start, smul(k, scan))) for k in range(1, L + 1)]
    H = 2 * (L + 1) - (0 if elongated else 1)
    headStart = add(bridgeJet, hS)
    headCopies = [shiftT(head, add(headStart, smul(k, hStep))) for k in range(1, H + 1)]
    return first, scanCopies + [bridgeTile] + headCopies


def correctionSchedule(saved, ancestor, beforePush, parity, flip, elongated):
    if not ancestor:
        raise CtorError('empty saved correction ancestor')
    last = ancestor[-1]
    L = max(0, len(beforePush) - len(ancestor))
    suffix = '2' if parity == 'odd' else '3'
    if beforePush != ancestor + suffix * L:
        raise CtorError('saved correction ancestor has the wrong suffix')
    return correctionPieces(saved, ancestor[:-1], last, beforePush, parity, flip, elongated, L)


def correctionPair(saved, beforePush, parity, elongated):
    """correctionPair: (left, right) = the flip-true and flip-false helpers, each evaluated and lower-left normalised.
    `saved` is the (word, registers) pair of the saved register set, as in NativeState."""
    ancestor, regs = saved
    out = []
    for flip in (True, False):
        first, rest = correctionSchedule(regs, ancestor, beforePush, parity, flip, elongated)
        out.append(llc(evalPlaced(first, rest)))
    return tuple(out)


# ---------- the native state ----------

def parentsFor(regs, digit):
    st, al = regs['st'], regs['al']
    return {
        'odd': llc(st['ro'] if digit == '3' else st['co']),
        'even': llc(st['re'] if digit == '2' else st['ce']),
        'altodd': llc(al['ro'] if digit == '3' else al['co']),
        'alteven': llc(al['re'] if digit == '2' else al['ce']),
    }


def nextRegisters(state, digit):
    cur_word, cur_regs = state['cur']
    beforePush = cur_word
    word = beforePush + digit
    P = parentsFor(cur_regs, digit)
    if digit == '1':
        odd = ordinaryStandard(P, word, 'odd')
        even = ordinaryStandard(P, word, 'even')
        altOdd = ordinaryAlternate(P, beforePush, digit, 'odd')
        altEven = ordinaryAlternate(P, beforePush, digit, 'even')
    elif digit == '2':
        short = correctionPair(state['savedTwo'], beforePush, 'odd', False)
        long_ = correctionPair(state['savedTwo'], beforePush, 'odd', True)
        odd = ordinaryStandard(P, word, 'odd')
        even = correctedStandard(P, short, beforePush, digit, 'even')
        altOdd = correctedAlternate(P, long_, beforePush, digit, 'odd')
        altEven = ordinaryAlternate(P, beforePush, digit, 'even')
    else:
        short = correctionPair(state['savedThree'], beforePush, 'even', False)
        long_ = correctionPair(state['savedThree'], beforePush, 'even', True)
        odd = correctedStandard(P, short, beforePush, digit, 'odd')
        even = ordinaryStandard(P, word, 'even')
        altOdd = ordinaryAlternate(P, beforePush, digit, 'odd')
        altEven = correctedAlternate(P, long_, beforePush, digit, 'even')
    regs = {
        'st': {'co': llc(odd), 'ce': llc(even), 'ro': P['odd'], 're': P['even']},
        'al': {'co': llc(altOdd), 'ce': llc(altEven), 'ro': P['altodd'], 're': P['alteven']},
    }
    return regs


def saveNext(state, digit, regs):
    cur_word, _ = state['cur']
    new = (cur_word + digit, regs)
    if digit == '1':
        return {'cur': new, 'savedTwo': new, 'savedThree': new}
    if digit == '2':
        return {'cur': new, 'savedTwo': state['savedTwo'], 'savedThree': new}
    return {'cur': new, 'savedTwo': new, 'savedThree': state['savedThree']}


def advance(state, digit):
    regs = nextRegisters(state, digit)
    return saveNext(state, digit, regs)


def baseRegisters(run_word):
    """The registers of a base run: the TeX standard and alternate tiles of the pure word, with the alternate retained
    pair taken from the TeX alternate state (the base runs' alternate retained tiles differ from the standard ones)."""
    word = run_word
    st_s = at.std_state(word)
    al_s = at.alt_state(word)
    st = {'co': llc(at.std_odd(word)), 'ce': llc(at.std_even(word)),
          'ro': llc(st_s[1]), 're': llc(st_s[2])}
    al = {'co': llc(at.alt_odd(word)), 'ce': llc(at.alt_even(word)),
          'ro': llc(al_s[3]), 're': llc(al_s[4])}
    return {'st': st, 'al': al}


def splitInitial(word):
    if word == '':
        return '', ''
    if word[0] in '1':
        return '', word
    d = word[0]
    k = 1
    while k < len(word) and word[k] == d:
        k += 1
    return word[:k], word[k:]


def evaluate(word):
    run, suffix = splitInitial(word)
    regs = baseRegisters(run) if run else {'st': {'co': llc(at.std_odd('')), 'ce': llc(at.std_even('')),
                                                   'ro': llc(at.std_state('')[1]), 're': llc(at.std_state('')[2])},
                                           'al': {'co': llc(at.alt_odd('')), 'ce': llc(at.alt_even('')),
                                                  'ro': llc(at.std_state('')[1]), 're': llc(at.std_state('')[2])}}
    saved = (run, regs)
    state = {'cur': saved, 'savedTwo': saved, 'savedThree': saved}
    for d in suffix:
        state = advance(state, d)
    return state


def output(word):
    """The outputs of the last step of `word`: (odd, even, altOdd, altEven), llCentered."""
    state = evaluate(word)
    regs = state['cur'][1]
    return regs['st']['co'], regs['st']['ce'], regs['al']['co'], regs['al']['ce']
