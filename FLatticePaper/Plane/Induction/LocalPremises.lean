import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.ZeroRegionBound
import FLatticePaper.Plane.Induction.HarmonicRegionBound
import FLatticePaper.Plane.Induction.SheetMinFromConj
import FLatticePaper.Plane.Induction.StarFromSheets
import FLatticePaper.Plane.Induction.RankFromForts

/-! The local premises of the induction step (task 21). `LocalPremises word` bundles the hypotheses of the five
reductions (I1, I2, I3, S1 with S2, S3) other than the conjugate Packet, which the induction supplies.

The sheet-difference identity `C − A + Φ' = K` holds with a constant `K` that the conjugate Packet determines, so the
chain bounds `Φ' ≤ K` (I1) and `K ≤ Φ'`, `Φ' ≤ K` (I2) are equivalent to sign conditions on `C − A`; `K` is then
eliminated inside the induction. -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

/-- The local premises at a proper word, for the sheets `A`, `C` of the conjugate standard field `Fp` (the chain
potential `Ξ`) and for the standard field `F` of the word. -/
def LocalPremises (word : Word) : Prop :=
  let frame := frameAt word
  let Fp := quarterTurnField (standardField (conjWord word))
  let F := standardField word
  let Ξ := sheetChainPotential word (standardField (conjWord word))
  -- I1: the sheet difference is nonnegative on the zero region of the closed polygon
  (∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z →
      0 ≤ frame.sheetC Fp z - frame.sheetA Fp z) ∧
  -- I2: the sheet difference has the sign of `ε` on the harmonic region
  (∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      (frame.eps = 1 → 0 ≤ frame.sheetC Fp z - frame.sheetA Fp z) ∧
      (frame.eps = -1 → frame.sheetC Fp z - frame.sheetA Fp z ≤ 0)) ∧
  -- I3: the chain potential has unit increments on edges, and the two permitted sides have constrained ranks
  (∀ c i : Site, FLatticePaper.Edge i c → -1 ≤ Ξ i - Ξ c ∧ Ξ i - Ξ c ≤ 1) ∧
  (∃ rankA : Site → ℤ, IsConstrainedBurningRank Fp rankA (fun c i => Ξ i ≤ Ξ c)) ∧
  (∃ rankC : Site → ℤ, IsConstrainedBurningRank Fp rankC
      (fun c i => Ξ (c + frame.sheetOffset) ≤ Ξ (i + frame.sheetOffset))) ∧
  -- S1, S2: the difference `D = F − F(· + σ)` takes values in {0, 1, 2} on E and its inputs, with no 0–2 edge
  (∀ e ∈ frame.closedPolygon, starDiff F frame.shortShift e = 0 ∨ starDiff F frame.shortShift e = 1 ∨
      starDiff F frame.shortShift e = 2) ∧
  (∀ e ∈ frame.closedPolygon, ∀ u, FLatticePaper.Edge u e →
      (starDiff F frame.shortShift u = 0 ∨ starDiff F frame.shortShift u = 1 ∨
        starDiff F frame.shortShift u = 2)) ∧
  (∀ e ∈ frame.closedPolygon, ∀ u, FLatticePaper.Edge u e →
      ¬((starDiff F frame.shortShift e = 0 ∧ starDiff F frame.shortShift u = 2) ∨
        (starDiff F frame.shortShift e = 2 ∧ starDiff F frame.shortShift u = 0))) ∧
  -- S3: the local permits and the absence of restricted forts in the grade half-spaces
  PermitLocal F (slipPermits F (fun z => F (z + frame.shortShift))) ∧
  RestrictedNoFort F frame.tGrade (slipPermits F (fun z => F (z + frame.shortShift)))

/-- The open inputs of the step follow from the local premises and the conjugate Packet. -/
theorem openInputs_of_localPremises {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hloc : LocalPremises word) : OpenInputs word := by
  dsimp only [LocalPremises] at hloc
  obtain ⟨hI1, hI2, hunit, ⟨rankA, hrankA⟩, ⟨rankC, hrankC⟩, -, -, -, -, -⟩ := hloc
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  have hI1' := openInput_one_of_chainBound h hG hK (fun z hz ht => by linarith [hK z, hI1 z hz ht])
  have hI2' := openInput_two_of_chainBound h hG hK (fun z hz hs =>
    ⟨fun he => by linarith [hK z, (hI2 z hz hs).1 he], fun he => by linarith [hK z, (hI2 z hz hs).2 he]⟩)
  have hI3 := sheetMin_binary_recurrent_of_chain h hG hunit rankA rankC hrankA hrankC
  unfold OpenInputs
  exact ⟨hI1', hI2', hI3.1⟩

/-- Every standard field has the packet, given the local premises at every proper word. -/
theorem packet_of_localPremises (h : ∀ w : Word, (∃ x ∈ w, x ≠ Digit.three) → LocalPremises w) :
    ∀ w : Word, (frameAt w).Packet (standardField w) := by
  refine word_induction (P := fun w => (frameAt w).Packet (standardField w)) ?_ ?_
  · intro k
    exact reciprocal_packet k
  · intro word hproper hIH
    obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hproper hIH
    obtain ⟨hC0, hGe, hbin⟩ := openInputs_of_localPremises hproper hIH (h word hproper)
    have hP := (frameAt word).packet_of_sheets (Fp := quarterTurnField (standardField (conjWord word)))
      hA0 hC0 hEq hGe hrefl hbin
    rw [standardField_proper hproper]
    exact hP

end FLatticePaper.Induction
