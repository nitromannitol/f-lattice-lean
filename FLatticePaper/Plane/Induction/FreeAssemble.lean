import FLatticePaper.Plane.Induction.FreePermittedS
import FLatticePaper.Plane.Induction.WordPolicy
import FLatticePaper.Plane.Induction.ForcedPriceSI

/-! The `FreeNamedInputs` of the word's free-edge signed policy, for a sign `η ∈ {±1}`.

The `permitted` field is `FreePermittedS.permitted_S`, `strictRank` is the aux rank of the sign restricted to the policy edges
(`AuxRankSign.freePolicy_aux`), and the rest is `WordPolicy.word_named_inputs`. The named inputs are the aux rank of sign η, `hwest`,
`OddBlackNoRise`, `W1Forced` (which gives `ForcedExists` by `forcedExists_of`), and the price premise `hfreeP` (which carries the N = 1
phase-one corner) together with the comparison data `EC`, `hT`, `hW` of `word_price_nonincreasing`, and the canonical games `G`. -/

namespace FLatticePaper.FreeAssemble

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.AuxRankSign FLatticePaper.FreeClosure
  FLatticePaper.WordPolicy FLatticePaper.SquareClauses

theorem free_named_inputs {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hWord : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hOdd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {R : Site → ℤ}
    (hstrictR : ∀ c i, auxS (frameAt word) (standardField word) η c i → R i < R c)
    (hfreeP : ∀ c i, laplacian (standardField word) c = 0 → freeClosure (frameAt word) c →
      FreePresc (frameAt word) η c i →
      (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c)
    (hwest : (frameAt word).eps = 1 → freePolicy (frameAt word) (standardField word) η
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1))) :
    FreeNamedInputs (frameAt word) (standardField word) η R := by
  have hsat : HasSatSelection (standardField word) := ForcedPriceSI.hasSat_of_aux η hη hWord hstrictR
  have hslip : ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c := by
    intro c i hci
    exact (FreePermitted.slipPermits_iff_slip η c i).mp (FreePermittedS.permitted_S h hWord hSE G hOdd hW1 hη hstrictR c i hci)
  have hex := forcedExists_of (frameAt word) hWord.packet hW1
  have hstrict : ∀ c i, freePolicy (frameAt word) (standardField word) η c i → R i < R c := by
    intro c i hci
    exact hstrictR c i (freePolicy_aux η hη hex (evenSite_shortShift (frameAt word)) hWord.packet.binary
      hWord.F1_unitSlip (CanonicalPermit.standardField_reflect hWord) hstrictR hci)
  exact
    { permitted := FreePermittedS.permitted_S h hWord hSE G hOdd hW1 hη hstrictR
      nonincreasingP := fun c i hci => by
        have hm := ForcedPriceSI.word_price_nonincreasing_SI word h hSE hWord hW1 hsat η hfreeP c i hci
        rw [cutGrade_one_zero_one, cutGrade_one_zero_one]
        exact hm
      nonincreasingJ := WordPolicy.word_J_nonincreasing word η hslip
      strictRank := hstrict
      westAtException := hwest }

end FLatticePaper.FreeAssemble
