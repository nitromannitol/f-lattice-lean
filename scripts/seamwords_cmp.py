"""Task 54 numerics: compare the Lean recursion words (checks/SeamWords.lean output) with the arcs of the actual tiles
traced from the lower-left vertex (0,0). The Lean lines are `W digits | OB w1 | OR w2 | EB v1 | ER v2`.
The tile arcs: w1, w2 are the first and second forward arcs of the loop from (0,0) of cellTile(oddTile w) (resp. evenTile).
Usage: python3 seamwords_cmp.py LEANLOG"""
import sys
from collections import Counter
from standard_tiles import oddTile, evenTile, cellTile
from seamchain import walk_from, split_forward

NAME = {(1, 0): "1", (0, 1): "i", (-1, 0): "-1", (0, -1): "-i"}


def tile_arcs(T):
    loop = walk_from(T, (0, 0))
    if loop is None: return None
    sp = split_forward(loop)
    if sp is None: return None
    return [",".join(NAME[d] for d in part) for part in sp]


if __name__ == "__main__":
    cnt = Counter(); bad = []
    for line in open(sys.argv[1]):
        if not line.startswith("W"): continue
        parts = [p.strip() for p in line.split("|")]
        digits = parts[0][1:].strip()
        w = tuple(int(ch) for ch in digits)
        ob = parts[1].split(" ", 1)[1]; orr = parts[2].split(" ", 1)[1]
        eb = parts[3].split(" ", 1)[1]; er = parts[4].split(" ", 1)[1]
        for kind, T, lb, lr in (("odd", cellTile(oddTile(w)), ob, orr), ("even", cellTile(evenTile(w)), eb, er)):
            cnt[(kind, "words")] += 1
            arcs = tile_arcs(T)
            if arcs is None:
                cnt[(kind, "no_forward_loop")] += 1; bad.append((digits, kind, "loop")); continue
            a1, a2 = arcs[0], arcs[1]
            # the Lean words are the first two arcs of the loop from (0,0) (the empty arc prints as nothing)
            m1 = (a1 == lb) or (a1 == "" and lb == "")
            m2 = (a2 == lr) or (a2 == "" and lr == "")
            cnt[(kind, "bottom_word_is_arc1")] += m1
            cnt[(kind, "right_word_is_arc2")] += m2
            if not (m1 and m2) and len(bad) < 6: bad.append((digits, kind, lb, a1, lr, a2))
    for k in sorted(cnt, key=str): print(k, cnt[k])
    print("mismatches (first):", bad[:6])
