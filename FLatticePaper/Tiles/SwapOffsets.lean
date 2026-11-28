import FLatticePaper.Tiles.GlueFull

/-! # The offsets of the pieces of the odd and even children, in terms of the parents

The offsets `offO w k` (odd child, `k < 6`) and `offE w k` (even child) are read off the piece lists `oddP`, `oddQ`, `evenP`,
`evenQ` of `ChildGlue`, which are linear in the two parent fractions `p = (parentsAt w).odd`, `q = (parentsAt w).even` and the
phase flag `W1Odd w`. These are the twelve formulas used to compute the pieces of the one-base clauses of `SwapBaseInput`. -/

namespace FLatticePaper.Tiles.SwapOffsets

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.GlueFull FLatticePaper.Tiles.JointFamily
open FLatticePaper.Construction (texV1Odd texV1Even texV2)

theorem offO_0 (w : Word) : offO w 0 =
    if W1Odd w then 0 else texV1Even (parentsAt w).even + texV1Even (parentsAt w).even := by
  unfold offO W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.oddP, FLatticePaper.Tiles.MixedPieces.pOffsetsOdd, h]

theorem offO_1 (w : Word) : offO w 1 =
    if W1Odd w then texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even
    else texV2 (parentsAt w).even := by
  unfold offO W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.oddP, FLatticePaper.Tiles.MixedPieces.pOffsetsOdd, h]

theorem offO_2 (w : Word) : offO w 2 = if W1Odd w then texV1Odd (parentsAt w).odd else 0 := by
  unfold offO W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.oddQ, FLatticePaper.Tiles.MixedPieces.qOffsetsOdd, h]

theorem offO_3 (w : Word) : offO w 3 =
    if W1Odd w then texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even else texV1Even (parentsAt w).even := by
  unfold offO W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.oddQ, FLatticePaper.Tiles.MixedPieces.qOffsetsOdd, h]

theorem offO_4 (w : Word) : offO w 4 =
    if W1Odd w then texV2 (parentsAt w).odd else texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd := by
  unfold offO W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.oddQ, FLatticePaper.Tiles.MixedPieces.qOffsetsOdd, h]

theorem offO_5 (w : Word) : offO w 5 =
    if W1Odd w then texV2 (parentsAt w).odd + texV1Even (parentsAt w).even
    else texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + texV1Even (parentsAt w).even := by
  unfold offO W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.oddQ, FLatticePaper.Tiles.MixedPieces.qOffsetsOdd, h]

theorem offE_0 (w : Word) : offE w 0 = if W1Odd w then 0 else texV1Even (parentsAt w).even := by
  unfold offE W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.evenP, FLatticePaper.Tiles.MixedPieces.pOffsetsEven, h]

theorem offE_1 (w : Word) : offE w 1 =
    if W1Odd w then texV2 (parentsAt w).odd else texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
  unfold offE W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.evenP, FLatticePaper.Tiles.MixedPieces.pOffsetsEven, h]

theorem offE_2 (w : Word) : offE w 2 =
    if W1Odd w then texV1Even (parentsAt w).even + texV2 (parentsAt w).even else texV2 (parentsAt w).even := by
  unfold offE W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.evenP, FLatticePaper.Tiles.MixedPieces.pOffsetsEven, h]

theorem offE_3 (w : Word) : offE w 3 =
    if W1Odd w then texV1Even (parentsAt w).even + texV2 (parentsAt w).even + texV2 (parentsAt w).odd
    else texV2 (parentsAt w).even + texV2 (parentsAt w).odd := by
  unfold offE W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.evenP, FLatticePaper.Tiles.MixedPieces.pOffsetsEven, h]

theorem offE_4 (w : Word) : offE w 4 = if W1Odd w then texV1Odd (parentsAt w).odd else 0 := by
  unfold offE W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.evenQ, FLatticePaper.Tiles.MixedPieces.qOffsetsEven, h]

theorem offE_5 (w : Word) : offE w 5 =
    if W1Odd w then texV2 (parentsAt w).odd + texV2 (parentsAt w).odd
    else texV1Odd (parentsAt w).odd + (texV2 (parentsAt w).odd + texV2 (parentsAt w).odd) := by
  unfold offE W1Odd
  cases h : phase w == 1 <;> simp [FLatticePaper.Tiles.ChildGlue.evenQ, FLatticePaper.Tiles.MixedPieces.qOffsetsEven, h]

end FLatticePaper.Tiles.SwapOffsets
