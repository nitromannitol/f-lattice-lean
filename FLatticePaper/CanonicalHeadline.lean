import FLatticePaper.StrongHeadline
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.W1Strips

/-! Task 71: the odometers headline with the canonical signed policy at every proper word, in place of the old policy `hpol`.
`hcan` supplies, at each proper word `w`, a canonical signed policy of the conjugate `conjWord w`; `oldPolicyData_of_canonical`
turns it into the old policy data with the empty seed, which `odometersTheorem_of_policy` consumes. The other hypotheses are those
of `odometersTheorem_of_policy`. -/

namespace FLatticePaper

open Farey Induction

/-- The reflection of the standard field of a conjugate word, from its strong estimates (`standardField_iRefl`): `F (I − z) = F z`. -/
theorem standardField_reflectI_conj (word : Word) (h : Induction.StrongEstimates (conjWord word)) (z : Site) :
    standardField (conjWord word) (reflectionI - z) = standardField (conjWord word) z := by
  have := FLatticePaper.W1Strips.standardField_iRefl h z
  rw [FLatticePaper.W1Strips.iRefl_eq_sub] at this
  exact this

/-- **The odometers theorem from the canonical signed policy (task 71).** -/
theorem odometersTheorem_of_canonical
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word)
    (hcan : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Nonempty (Induction.CanonicalSignedPolicy (frameAt (conjWord word)) (standardField (conjWord word))))
    (hResP : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
        c ∈ (frameAt word).closedPolygon →
        (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hResN : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
        c ∈ (frameAt word).closedPolygon →
        (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False)
    (hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word)) :
    OdometersTheorem := by
  have hE : ∀ word : Word, Induction.StrongEstimates word :=
    Induction.strongEstimates_of_residual_all
      (fun k => Induction.StrongEstimates.of_base_pure k (hpureSlip k) (hpureRes k))
      (fun k => Induction.StrongEstimates.of_base_two k (htwoSlip k) (htwoRes k)) hres
  exact odometersTheorem_of_policy hpureSlip hpureRes htwoSlip htwoRes hres
    (fun word hw hn => ⟨fun _ _ => False, ⟨Induction.oldPolicyData_of_canonical
      (standardField_reflectI_conj word (hE (conjWord word))) (hcan word hw hn).some⟩⟩)
    hResP hResN hbulk

end FLatticePaper
