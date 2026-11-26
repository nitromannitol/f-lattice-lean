import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.HResPWire
import FLatticePaper.Plane.Induction.HResNCases
import FLatticePaper.Plane.Induction.CanonicalPermit
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.NegTieHCutFinal
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! `OddBlackNoRise` of the word, as a step theorem.

The conjugate's old policy comes from its games (`hG`, through `games_of_gamesWithRank` and `oldPolicyData_of_canonical`). The slip
range and the unit slip are discharged by the conjugate's strong estimates (`TieReduce`). The two narrowed sheet-tie leaves
`hResP`, `hResN` are discharged from the V-block input `hQ21` (`HResPWire.hResP_of_Q21`, `HResPWire.hNegTie_of_Q21`,
`HResNCases.hResN_of_cases`). The V-block input `hQ21` is proved (`NegTieHCutFinal.H_cut_hQ21`, lifted here as `hQ21_of_old`).
The named step leaves are therefore `hpar` (the conjugate's seed fields, carried by the induction) and `hW1c` (the conjugate's
`W1Forced`, the induction's W1 hypothesis). -/

namespace FLatticePaper.OddBlackStep

open Farey FLatticePaper FLatticePaper.Induction

/-- **The V-block input `hQ21`, proved.** From the conjugate's old policy and the word's packet and slip range, the negative rising
pair with a tied centre is excluded at every translate: the content of `NegTieHCutFinal.H_cut_hQ21`, in the shape used by the
tie leaves (`HResPWire`, `HResNCases`). -/
theorem hQ21_of_old {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2) :
    ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 0 ≤ sheetDiffW word i →
      ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
        zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False := by
  intro c i hr hcE hiE hcu hiu hΨc hΨj hΨi
  obtain ⟨j, hj, hjΨ⟩ := hΨj
  exact H_cut_hQ21 h hSE hpk P hslip hr hcE hiE hcu hiu hΨc hj hjΨ hΨi

/-- **`OddBlackNoRise` of the word**, from the conjugate's games (`hG`), the conjugate's seed fields (`hpar`) and `W1Forced` (`hW1c`),
which the induction carries. The V-block input is `hQ21_of_old`. -/
theorem oddBlackNoRise_step {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hWord : StrongCore word)
    (hSE : StrongEstimates (conjWord word)) (hG : GamesWithRank (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hW1c : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word))) :
    OddBlackNoRise (standardField word) (frameAt word).shortShift := by
  obtain ⟨G⟩ := games_of_gamesWithRank hG
  have hη : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := ChildFrame.eps_unit (frameAt word)
  let P := oldPolicyData_of_canonical (CanonicalPermit.standardField_reflect hSE) G (frameAt word).eps hη
  have hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2 := by
    intro z hz
    have hs := hWord.slipRange z hz
    simpa [ChildFrame.slip] using hs
  have hQ21 := hQ21_of_old h hSE hWord.packet P hslip
  exact oddBlackNoRise_of_narrow h hSE P (hResP_of_Q21 h hWord hSE hpar P hW1c hQ21)
    (fun c i hr hcE huu hΨc hj =>
      hResN_of_cases h hSE hWord.packet P (hNegTie_of_Q21 h hWord hSE hpar P hW1c hQ21) hr hcE huu.1 huu.2 hΨc hj)

end FLatticePaper.OddBlackStep
