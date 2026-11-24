import FLatticePaper.Plane.Induction.StrongBridge
import FLatticePaper.Plane.Induction.StrongResidualStep
import FLatticePaper.Plane.Induction.W1BaseSeeds
import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.TwosInduction

/-!
# The strong estimates and the seed fields of every word, by one induction (the headline's residual inputs)

`strongSeeds_of_all`: `StrongEstimates word ∧ SeedFields word` for every word, by the word induction. The base cases are the pure words
(`seedFields_threes`) and the two-powers (`seedFields_two_succ`, from the pure word's estimates). The step at a proper word that is not a
two-power takes the conjugate's estimates and seeds `(S, P)`, and gives the residual by `strongResidual_of_conj` (which takes the seeds of
the conjugate, the boundary bound `hbd` and the policy `hpol` of the word) and the estimates by `strongEstimates_step_strong`; the seeds of
the word come from `seedFields_of_conj`.

So the only per-word inputs of the headline are `hbd` (the boundary bound, Q22) and `hpol` (the policy of the word, Q1).
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- A word that is not a power of two has a digit other than `two`, provided it has a digit other than `three`. -/
theorem exists_ne_two_of_not_twoPow {word : Word} (hproper : ∃ x ∈ word, x ≠ Digit.three) (hI : ¬ IsTwoPow word) :
    ∃ x ∈ word, x ≠ Digit.two := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hI
  obtain ⟨x, hx, -⟩ := hproper
  have hlen : word.length ≠ 0 := by
    intro h0
    rw [List.length_eq_zero_iff] at h0
    rw [h0] at hx
    simp at hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, word.length = k + 1 := ⟨word.length - 1, by omega⟩
  exact ⟨k, List.eq_replicate_iff.mpr ⟨hk, fun b hb => hcon b hb⟩⟩

/-- **The strong estimates and the seed fields of every word**, by the word induction from the pure words and the two-powers. -/
theorem strongSeeds_of_all
    (hpure : ∀ k : ℕ, StrongEstimates (List.replicate k Digit.three))
    (htwo : ∀ k : ℕ, StrongEstimates (List.replicate (k + 1) Digit.two))
    (hbd : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hpol : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
        RetainQuota (standardField word) policy ∧
        NonincreasingAlong ((frameAt word).chainPotential (standardField word) η) policy ∧
        NonincreasingAlong ((frameAt word).price (standardField word)) policy ∧
        NonincreasingAlong ((frameAt word).roundedSlip (standardField word) η) policy ∧
        (∀ z, R (z + (frameAt word).child.modifiedDeck.kernel) = R z + cU) ∧
        (∀ z, R (z + (frameAt word).child.modifiedDeck.transverse) = R z + cV) ∧
        (∀ x i, policy x i → R i < R x)) :
    ∀ word : Word, StrongEstimates word ∧ W1Seeds.SeedFields word := by
  refine word_induction (P := fun word => StrongEstimates word ∧ W1Seeds.SeedFields word)
    (fun k => ⟨hpure k, W1BaseSeeds.seedFields_threes k⟩) ?_
  intro word hproper ih
  obtain ⟨hS, hpar⟩ := ih
  by_cases hI : IsTwoPow word
  · obtain ⟨k, rfl⟩ := hI
    exact ⟨htwo k, W1BaseSeeds.seedFields_two_succ k (hpure k)⟩
  · have hR : StrongResidual word :=
      strongResidual_of_conj hproper (exists_ne_two_of_not_twoPow hproper hI) hS (hbd word hproper hI) hpar
        (hpol word hproper hI)
    exact ⟨strongEstimates_step_strong hproper hS hR,
      W1SeedFields.seedFields_of_conj hproper hS hpar⟩

end FLatticePaper.Induction
