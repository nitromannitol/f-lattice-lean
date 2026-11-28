import FLatticePaper.Tiles.LSidesOddV

/-! # The vertical sides of the odd L-corrections in the triple case `pre = 3^j`

For `w = 3^j 2^k` (`j ≥ 1`) the odd register of `3^j` is the initial tile `T_{0/1}`, so the bridge of the odd L-correction is
`T_{0/1}` (shifted by `LCorrections.oddBridgeShift`), and at `k = 0` the word `3^j` is a base word, whose odd tile odometer is the
base odometer. The vertical side of the odd child is covered by the stems and the bridge as for the other prefixes; at the base
word this is the base fact `TripleBaseInput` below (numerically, the odd base odometer of `3^j` contains the whole first stem and
the whole shifted bridge, each up to one constant, for `j ≤ 6` and both signs). -/

namespace FLatticePaper.Tiles.LSidesOddTriple

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.LSidesOddV (PlacedEqA)
open FLatticePaper.Tiles.TileHalfTurnL (oBridgePos oAffAt oBridgeC)

/-- **The base fact of the triple case `pre = 3^j`** (`j ≥ 1`), for the vertical sides of the odd L-corrections of `3^j`: the odd
base odometer `O` of `3^j` contains the even base odometer `E'` of `3^{j-1}` at the first stem and the initial odometer `o_{0/1}`
at the shifted bridge, each with the affine factor of the L-correction and up to a constant, and these two copies cover the
vertical side of the odd base tile that the L-correction contains (the left side for `+`, the right side for `-`; `W_1` is even
at `3^j`). Stated, not proved here. -/
def TripleBaseInput : Prop :=
  ∀ (j : ℕ), 1 ≤ j → ∀ (O E O' E' : PartialOdometer), SurgicalWeak.PaperBaseCond (List.replicate j Digit.three) O E →
    SurgicalWeak.PaperBaseCond (List.replicate (j - 1) Digit.three) O' E' → ∀ plus : Bool,
      PlacedEqA O E' (oddLInitOff (List.replicate j Digit.three) plus) (oddLInitAff (List.replicate j Digit.three) plus) ∧
      PlacedEqA O paperS.zeroO
        (oBridgePos (List.replicate j Digit.three) plus + LCorrections.oddBridgeShift true false plus)
        (oAffAt (List.replicate j Digit.three) plus (oBridgeC (List.replicate j Digit.three) plus)) ∧
      ∀ x ∈ placedSites (sideString (hWordOf (List.replicate j Digit.three) false)
          (vWordOf (List.replicate j Digit.three) false) 0 (if plus then .vMinus else .vPlus)),
        x - oddLInitOff (List.replicate j Digit.three) plus ∈ E'.dom ∨
          x - (oBridgePos (List.replicate j Digit.three) plus + LCorrections.oddBridgeShift true false plus) ∈
            paperS.zeroO.dom

end FLatticePaper.Tiles.LSidesOddTriple
