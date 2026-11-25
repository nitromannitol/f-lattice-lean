import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.HResPWire
import FLatticePaper.Plane.Induction.HResNCases
import FLatticePaper.Plane.Induction.CanonicalPermit
import FLatticePaper.Plane.Induction.GamesPolicy

/-! `OddBlackNoRise` of the word, as a step theorem.

The conjugate's old policy comes from its games (`hG`, through `games_of_gamesWithRank` and `oldPolicyData_of_canonical`). The slip
range and the unit slip are discharged by the conjugate's strong estimates (`TieReduce`). The two narrowed sheet-tie leaves
`hResP`, `hResN` are discharged from the V-block input `hQ21` (`HResPWire.hResP_of_Q21`, `HResPWire.hNegTie_of_Q21`,
`HResNCases.hResN_of_cases`). The named leaves are therefore `hQ21` (the Q21 V-block input), `hpar` (the conjugate's seed fields)
and `hW1c` (the conjugate's `W1Forced`). -/

namespace FLatticePaper.OddBlackStep

open Farey FLatticePaper FLatticePaper.Induction

theorem oddBlackNoRise_step {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hWord : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word)) (hG : GamesWithRank (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hW1c : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hQ21 : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 0 ≤ sheetDiffW word i →
      ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
        zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False) :
    OddBlackNoRise (standardField word) (frameAt word).shortShift := by
  obtain ⟨G⟩ := games_of_gamesWithRank hG
  have hη : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := ChildFrame.eps_unit (frameAt word)
  let P := oldPolicyData_of_canonical (CanonicalPermit.standardField_reflect hSE) G (frameAt word).eps hη
  exact oddBlackNoRise_of_narrow h hSE P (hResP_of_Q21 h hWord hSE hpar P hW1c hQ21)
    (fun c i hr hcE huu hΨc hj =>
      hResN_of_cases h hSE hWord.packet P (hNegTie_of_Q21 h hWord hSE hpar P hW1c hQ21) hr hcE huu.1 huu.2 hΨc hj)

end FLatticePaper.OddBlackStep
