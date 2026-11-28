import FLatticePaper.Tiles.LSidesOddH

/-! # Two base facts for the horizontal sides of the odd L-corrections

Statements only, proved elsewhere (base cases).

* `BaseAltBottomInput`: at a base word `u` the forward horizontal string of `w_h(q₀)` at the origin lies in the even alternate
  tile of `u` (the base analogue of `lemma:alternate_tile_properties` (3), which `AltItem3.alt_item3_even` gives at the other
  words). Numerically true for `u = ()`, `3^j`, `2^j`, `j ≤ 6` (`tmp-w5/lsides/basefacts.py`).
* `TripleBottomBaseInput`: at `3^j` (`j ≥ 1`) the bottom string of the odd base tile is covered by the bottom strings of two
  copies of the even base tile of `3^{j-1}`, at `0` and at `v_{q,1}`, and by the copy of `T_{0/1}` at the shifted bridge of the
  `-` odd L-correction; the odd base odometer agrees with the even base odometer of `3^{j-1}` up to a constant on the bottom
  string of each copy and with `o_{0/1}` on the whole bridge (affine factors `0`). Numerically true for `j ≤ 6` (constants `0`;
  on the whole second copy the difference takes two values, so the agreement is stated on its bottom string only). -/

namespace FLatticePaper.Tiles.LSidesBaseFacts

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Even)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.LSidesOddV (PlacedEqA)
open FLatticePaper.Tiles.LSidesOddH (StrEq)
open FLatticePaper.Tiles.TileHalfTurnL (oBridgePos)

/-- **The forward horizontal string at the origin lies in the even alternate tile, at a base word.** Stated, not proved here. -/
def BaseAltBottomInput : Prop :=
  ∀ u : Word, IsBase u → ∀ x ∈ placedSites (hStringAt (hWordOf u true) 0),
    x ∈ SurgicalAltTiles.altEvenTile PaperAltBase.paperAltBaseTiles u

/-- **The bottom string of the odd base tile of `3^j`** (`j ≥ 1`), for the horizontal side of the `-` odd L-correction. Stated, not
proved here. -/
def TripleBottomBaseInput : Prop :=
  ∀ (j : ℕ), 1 ≤ j → ∀ (O E O' E' : PartialOdometer), SurgicalWeak.PaperBaseCond (List.replicate j Digit.three) O E →
    SurgicalWeak.PaperBaseCond (List.replicate (j - 1) Digit.three) O' E' →
      StrEq O E' (hStringAt (hWordOf (List.replicate (j - 1) Digit.three) true) 0) 0 0 ∧
      StrEq O E' (hStringAt (hWordOf (List.replicate (j - 1) Digit.three) true) 0)
        (texV1Even (parentsAt (List.replicate j Digit.three)).even) 0 ∧
      PlacedEqA O paperS.zeroO
        (oBridgePos (List.replicate j Digit.three) false + LCorrections.oddBridgeShift true false false) 0 ∧
      ∀ x ∈ placedSites (hStringAt (hWordOf (List.replicate j Digit.three) false) 0),
        x ∈ placedSites (hStringAt (hWordOf (List.replicate (j - 1) Digit.three) true) 0) ∨
          x - texV1Even (parentsAt (List.replicate j Digit.three)).even ∈
            placedSites (hStringAt (hWordOf (List.replicate (j - 1) Digit.three) true) 0) ∨
          x - (oBridgePos (List.replicate j Digit.three) false + LCorrections.oddBridgeShift true false false) ∈
            paperS.zeroO.dom

end FLatticePaper.Tiles.LSidesBaseFacts
