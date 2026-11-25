import FLatticePaper.Plane.Induction.Q30Strips
import FLatticePaper.Plane.Induction.TraceStep

/-! # The north-west middle of a game fort, per word

The per-word form of `Q30Strips.game_NW_of_strong`. Its two word-level premises are explicit here:

* `hT : TraceFromPsi.TraceAt word`: the trace of the word. Provider: `TraceStep.traceAt_step` (TraceStep.lean:106), from the
  conjugate's strong estimates and the trace of the earlier word; the base `3^k` is `PureTrace.traceAt_threes`.
* `hseed : W1Seeds.SeedFields word`: the seed fields of the word. Provider: `W1SeedFields.seedFields_of_conj` from the conjugate's
  seed fields (and `W1Seeds`' base words).

The boundary price bound `hbd` of `game_NW_of_strong` is `TraceStep.hbd_of_traceAt` applied to `hT`. The final `hW1` assembly
supplies `hT` and `hseed` from the same induction over words. -/

namespace FLatticePaper.Q30Strips

open FLatticePaper FLatticePaper.Induction FLatticePaper.Farey

/-- **The north-west middle per word.** A strict white free vertical root of a game fort, with its NW corner in `S` by the
`game_NW` argument, given the trace and the seed fields of the word (the inputs `hT`, `hseed` of the induction). -/
theorem game_NW_per_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hT : FLatticePaper.TraceFromPsi.TraceAt word)
    (hseed : FLatticePaper.W1Seeds.SeedFields word) {S : Set Site}
    (hG : FLatticePaper.GameFort.IsGameFort (frameAt word) (-1) (standardField word) S)
    {z : Site} (hzS : z ∈ S) (hzV : z ∈ (frameAt word).freeV) (hzH : z ∉ (frameAt word).freeH) (ho : ¬ EvenSite z)
    (hzW : laplacian (standardField word) z = 0)
    (hS1 : 2 * (frameAt word).child.num + 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤ (frameAt word).sGrade z)
    (hS2 : (frameAt word).sGrade z ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (ht1 : (frameAt word).child.num + (frameAt word).child.den - 1 - (frameAt word).child.periodDenominator
      + (frameAt word).child.den < (frameAt word).tGrade z)
    (ht2 : (frameAt word).tGrade z < (frameAt word).child.den) :
    (z.1 - 1, z.2 + 1) ∈ S :=
  game_NW_of_strong hw hSE (TraceStep.hbd_of_traceAt hw hSE hT) hseed hG hzS hzV hzH ho hzW hS1 hS2 ht1 ht2

end FLatticePaper.Q30Strips
