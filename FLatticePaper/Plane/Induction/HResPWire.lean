import FLatticePaper.Plane.Induction.NegTieSpan
import FLatticePaper.Plane.Induction.HResP

/-! Task 72 (wiring of hResP through the V block).

`hNegTie_of_Q21`: the negative tied-target exclusion `hNegTie` at a proper word, from the conjugate H-cut case `hQ21` (the V-block input
Q21, stated for the tie configuration), the conjugate `W1Forced` and the conjugate `SeedFields`. It is `negTie_false_of_V_block` with the
slip bound of `StrongEstimates`.

`hResP_of_Q21`: the tied rising pair `hResP` at a proper word, by `hResP_of_negTie` with `hNegTie_of_Q21`. The membership of the input
`i` in the polygon is `black_input_mem` (the centre is black and in the polygon). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The negative tied-target exclusion from the V-block input Q21.** -/
theorem hNegTie_of_Q21 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hE : StrongEstimates word) (hEc : StrongEstimates (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hQ21 : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 1 ≤ sheetDiffW word i →
      ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
        zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False) :
    ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 1 ≤ sheetDiffW word i → False := by
  intro c i hr hcE hiE hcu hiu hΨc hj hΨi
  obtain ⟨j, hjE, hjΨ⟩ := hj
  have hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2 := by
    intro z hz
    have hs := hE.slipRange z hz
    simpa [ChildFrame.slip] using hs
  exact negTie_false_of_V_block h hEc hE.packet hpar P hW1 hslip hr hcE hiE hcu hiu hΨc hjE hjΨ hΨi
    (hQ21 c i hr hcE hiE hcu hiu hΨc ⟨j, hjE, hjΨ⟩ hΨi)

/-- **The tied rising pair `hResP` from the V-block input Q21.** -/
theorem hResP_of_Q21 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hE : StrongEstimates word) (hEc : StrongEstimates (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hQ21 : ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
      c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
      c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 1 ≤ sheetDiffW word i →
      ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
        zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False) :
    ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon →
      (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
      sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False := by
  intro c i hr hcE hpair hΨc hj
  have hiE := (frameAt word).black_input_mem hE.packet hcE hr.2.1 hr.1
  exact hResP_of_negTie h hEc hE.packet P (hNegTie_of_Q21 h hE hEc hpar P hW1 hQ21) hr hcE hiE hpair.1 hpair.2 hΨc hj

end FLatticePaper.Induction
