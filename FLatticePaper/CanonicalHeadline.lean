import FLatticePaper.StrongHeadline
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.EPolicyFinal
import FLatticePaper.Plane.Induction.StrongSeedInduction

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
    (hbd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hpol : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
        RetainQuota (standardField word) policy ∧
        NonincreasingAlong ((frameAt word).chainPotential (standardField word) η) policy ∧
        NonincreasingAlong ((frameAt word).price (standardField word)) policy ∧
        NonincreasingAlong ((frameAt word).roundedSlip (standardField word) η) policy ∧
        (∀ z, R (z + (frameAt word).child.modifiedDeck.kernel) = R z + cU) ∧
        (∀ z, R (z + (frameAt word).child.modifiedDeck.transverse) = R z + cV) ∧
        (∀ x i, policy x i → R i < R x))
    (hcan : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Nonempty (Induction.CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word))))
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
  -- the strong estimates and the seed fields of every word, from the per-word inputs `hbd` and `hpol`
  have hJ := Induction.strongSeeds_of_all
    (fun k => Induction.StrongEstimates.of_base_pure k (hpureSlip k) (hpureRes k))
    (fun k => Induction.StrongEstimates.of_base_two k (htwoSlip k) (htwoRes k)) hbd hpol
  have hE : ∀ word : Word, Induction.StrongEstimates word := fun word => (hJ word).1
  have hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word :=
    fun word hw hn => Induction.strongResidual_of_conj hw (Induction.exists_ne_two_of_not_twoPow hw hn)
      (hE (conjWord word)) (hbd word hw hn) ((hJ (conjWord word)).2) (hpol word hw hn)
  exact odometersTheorem_of_policy hpureSlip hpureRes htwoSlip htwoRes hres
    (fun word hw hn => ⟨fun _ _ => False, ⟨Induction.oldPolicyData_of_canonical
      (standardField_reflectI_conj word (hE (conjWord word))) (hcan word hw hn).some (frameAt word).eps
      (frameAt word).eps_unit⟩⟩)
    hResP hResN hbulk

/-- The canonical signed games at the conjugate of a pure threes word, from `pure_threes_final` (`reciprocalFrame k` is
`frameAt (3^k)` and `standardField_threes` identifies the field). -/
theorem canonical_at_threes (word : Word) (hp : ∃ k : ℕ, conjWord word = List.replicate k Digit.three) :
    Nonempty (Induction.CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word))) := by
  obtain ⟨k, hk⟩ := hp
  have hf : frameAt (conjWord word) = reciprocalFrame k := by
    rw [hk]
    try rfl
  have hF : standardField (conjWord word) = reciprocalField k := by
    rw [hk, standardField_threes]
  rw [hf, hF]
  exact FLatticePaper.EPolicy.pure_threes_final.2.2 k

/-- **The odometers theorem from the canonical signed policy, with the pure threes inputs discharged (task 71).** The pure
threes inputs `BaseSlip` and `StrongResidual` come from `pure_threes_final`, and the canonical signed policy is required only
at the words whose conjugate is not a pure threes word. -/
theorem odometersTheorem_of_canonical_pure
    (htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two))
    (htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two))
    (hbd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hpol : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
        RetainQuota (standardField word) policy ∧
        NonincreasingAlong ((frameAt word).chainPotential (standardField word) η) policy ∧
        NonincreasingAlong ((frameAt word).price (standardField word)) policy ∧
        NonincreasingAlong ((frameAt word).roundedSlip (standardField word) η) policy ∧
        (∀ z, R (z + (frameAt word).child.modifiedDeck.kernel) = R z + cU) ∧
        (∀ z, R (z + (frameAt word).child.modifiedDeck.transverse) = R z + cV) ∧
        (∀ x i, policy x i → R i < R x))
    (hcan : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ¬ (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      Nonempty (Induction.CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word))))
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
    OdometersTheorem :=
  odometersTheorem_of_canonical FLatticePaper.EPolicy.pure_threes_inputs.1 FLatticePaper.EPolicy.pure_threes_inputs.2
    htwoSlip htwoRes hbd hpol
    (fun word hw hn => by
      by_cases hp : ∃ k : ℕ, conjWord word = List.replicate k Digit.three
      · exact canonical_at_threes word hp
      · exact hcan word hw hn hp)
    hResP hResN hbulk

end FLatticePaper
