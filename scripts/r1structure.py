"""Task 55 (R1 structure theorem, numerical form): the register words of the bottom recursion are the first arcs of the
register tiles.

Port of BottomEdges.lean: bottomEdges reads the word letter by letter with registers (regO, regE); before letter x the edges
e = prefixEdges(pre, regO, regE) are formed (base cases for all-2 and all-3 prefixes, edgeStep otherwise), and the registers
are updated by updateRegs. The final word bottomEdges(w) = prefixEdges(w, regs_w) and the registers regs_w are the state after
w. Checks, for every word of length 1..L (and the base words included):
  (A) (IOInv: some letter 1 or 2 is read) the odd register regs_w.0 equals the first arc of the register tile tO of state(w) (cellTile, traced from (0,0));
  (B) (IEInv: some letter 1 or 3 is read) the even register regs_w.1 equals the first arc of tE of state(w);
  (C) for non-base w: bottomEdges(w).0 == edgeStep(count1(w) odd, regs_w.0, regs_w.1).0 (definitional; checked as a sanity).
Usage: python3 r1structure.py L"""
import sys
from collections import Counter
from standard_tiles import words, state, cellTile
from seamwords_cmp import tile_arcs

def oneI(n): return ['1', 'i'] * n
def oneOne(n): return ['1', '1'] * n

def baseTwo(k): return (['1'] + oneI(2 * k + 1) + ['1', '1'], ['1'] + oneI(2 * k) + ['1', '1'])
def baseThree(k): return (oneOne(k) + ['1', 'i'] + oneOne(k + 1) + ['1'], ['1'] + oneOne(k + 1))

def edgeStep(odd, w, v):
    if odd: return (w + ['i'] + v + ['i'] + v, w + ['i'] + v)
    return (v + ['i'] + v + ['i'] + w, v + ['i'] + w)

def prefixEdges(u, regO, regE):
    if all(x == 2 for x in u): return baseTwo(len(u))
    if u and all(x == 3 for x in u): return baseThree(len(u))
    return edgeStep(sum(1 for x in u if x == 1) % 2 == 1, regO, regE)

def run(w):
    """Return (regs after w, bottomEdges(w))."""
    pre = []; regO = []; regE = []
    for x in w:
        e = prefixEdges(pre, regO, regE)
        if x == 1: regO, regE = e
        elif x == 2: regO, regE = e[0], regE
        else: regO, regE = regO, e[1]
        pre = pre + [x]
    return (regO, regE), prefixEdges(list(w), regO, regE)

def letters_of(arc):
    return [{"1": "1", "i": "i", "-1": "-1", "-i": "-i"}[t] for t in arc.split(",") if t]

def main(L):
    cnt = Counter(); bad = []
    for w in words(L):
        if not w: continue
        (rO, rE), _ = run(w)
        par, tO, tE = state(w)
        arcsO = tile_arcs(cellTile(tO)); arcsE = tile_arcs(cellTile(tE))
        cnt["words"] += 1
        if arcsO is not None and any(x in (1, 2) for x in w):
            ok = [t for t in letters_of(arcsO[0])] == rO
            cnt["A_odd_reg_is_tile_arc" if ok else "A_mismatch"] += 1
            if not ok and len(bad) < 3: bad.append(("A", ''.join(map(str, w)), rO[:8], letters_of(arcsO[0])[:8]))
        if arcsE is not None and any(x in (1, 3) for x in w):
            ok = [t for t in letters_of(arcsE[0])] == rE
            cnt["B_even_reg_is_tile_arc" if ok else "B_mismatch"] += 1
            if not ok and len(bad) < 3: bad.append(("B", ''.join(map(str, w)), rE[:8], letters_of(arcsE[0])[:8]))
    for k in sorted(cnt): print(k, cnt[k])
    print("examples of mismatch:", bad)

if __name__ == "__main__":
    main(int(sys.argv[1]))
