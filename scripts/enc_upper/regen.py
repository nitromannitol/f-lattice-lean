# Regenerates FLatticePaper/Tiles/EncFam.lean and EncPieces.lean from the margin identities (sympy).
# Run: python3 scripts/enc_upper/regen.py && python3 scripts/enc_upper/emit_final2.py
import sys
from emit2 import emit_branch, emit_top
parts = []
for m in (1, 2):
    for dl in (1, -1):
        for f in 'PQ':
            for parity in ('even', 'odd'):
                for branch in ('below', 'above'):
                    o, nm = emit_branch(m, dl, f, parity, branch)
                    parts.append("\n".join(o))
            o, nm = emit_top(m, dl, f)
            parts.append("\n".join(o))
hdr = """import FLatticePaper.Tiles.EncUpper

/-! Task 53, item 2 (encOdd / encEven): the lower facets of the six natural sources, one family per
(child type, flag, source parent), split by site parity and side. Generated from the margin identities
(sympy: lex remainder and quotient); each margin is `linarith` from its quotient and remainder. -/

namespace FLatticePaper.Tiles.EncFam

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.EncUpper

"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
path = os.path.join(HERE, "..", "..", "FLatticePaper", "Tiles", "EncFam.lean")
open(path, "w").write(hdr + "\n\n".join(parts) + "\n\nend FLatticePaper.Tiles.EncFam\n")
print("written", len(parts), "declarations-blocks")
