import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.SiteStrings

/-! # The vertical base pieces of the odd `3^k` word: the vertical word

For the odd child of `3^k`, the vertical word is `p^(2k+1) q` (`vWordOf (replicate k three) false`), obtained from the quadruple of
`2^k` (`RegisterLink.quad_twos`) through the exchange of `2` and `3`. The reversed vertical piece `Vm` reads its letters as
`q p^(2k+1)`, the first tile being the `one` tile at `(0,0)` and the others `zero` tiles, as in `BaseVertPilot`. -/

namespace FLatticePaper.Tiles.BaseVertPiece

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings

theorem vWordOf_three_false (k : ℕ) :
    vWordOf (List.replicate k Digit.three) false = List.replicate (2 * k + 1) Letter.p ++ [Letter.q] := by
  unfold vWordOf
  rw [FLatticePaper.Tiles.AltRotStep.swapW_replicate_three, if_neg Bool.false_ne_true,
    (RegisterLink.quad_twos k).2.1]
  simp [List.map_append, swapLetter]

end FLatticePaper.Tiles.BaseVertPiece
