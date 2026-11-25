import FLatticePaper.Plane.Induction.TwosRank
import FLatticePaper.Plane.Induction.TwosTileRange

/-! The strictness of the twos rank (sign `+1`) with `hvar` proved: only the flat-edge fact `hflat` is named.

`twosRank_strict_of_flat` is `twosRank_strict` with the range of the deck rank supplied by `tr_hvar` (the values of `deckAt` at the
native points lie in `[0, 2a+1]`, `TwosTileRange`). The remaining named input is `hflat`: `ρ` drops along the selected edges on which
`Φ` is flat (numerically the step is a unit move, and `ρ` drops by exactly `1`, for `a = 4, 6, 8`). -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

theorem twosRank_strict_of_flat (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (hflat : ∀ c i : Site, TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c →
      rhoTwos (2 * (k : ℤ) + 4) 1 i < rhoTwos (2 * (k : ℤ) + 4) 1 c)
    {c i : Site}
    (hT : TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i) :
    twosRank k i < twosRank k c :=
  twosRank_strict k hagree hperiod (tr_hvar k) hflat hT

end FLatticePaper.TwosEPolicy
