import FLatticePaper.Plane.Induction.EPolicyValues
import FLatticePaper.Plane.Induction.WeightPolicy
import FLatticePaper.Plane.Induction.PureBasePrice
import FLatticePaper.Plane.Induction.SlipBase
import FLatticePaper.Plane.Induction.ResidualPure
import FLatticePaper.Plane.Induction.BaseSlipPure

/-! The policy field `F2F3_policy` of `StrongResidual` at `3^k`, assembled from `ReciprocalValues k` and the rank with increments.

For the policy `ePolicy (2d+3) η (laplacian F)` with `F = reciprocalField k`:
* the quota is `retainQuota_e`, and the chain monotonicity is the `chain` field;
* the weights `(−a, c η)`, for all positive `a, c`, come from ONE rank with increments `(−1, η)` (`hrank`), by the monotone hull lemma
  `rankWithIncrements_of_monotone_hull`, with `P` the price (drifts `priceDrift_threes`) and `J = roundedSlip η` (invariant under the
  kernel, `+η` under the transverse period, `slipDrift_threes`), both nonincreasing along the policy (the `slip` field). -/

namespace FLatticePaper.EPolicy

open Farey FLatticePaper FLatticePaper.Induction
open FLatticePaper.Construction

theorem F2F3_threes_of_values (k : ℕ) (V : ReciprocalValues k)
    (hrank : ∀ η : ℤ, (η = 1 ∨ η = -1) →
      RankWithIncrements (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)))
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-1) η) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
      RetainQuota (standardField (List.replicate k Digit.three)) policy ∧
        NonincreasingAlong ((frameAt (List.replicate k Digit.three)).chainPotential
          (standardField (List.replicate k Digit.three)) η) policy ∧
        ∀ a c : ℤ, 0 < a → 0 < c →
          RankWithIncrements policy (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
            (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-a) (c * η) := by
  intro η hη
  refine ⟨ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)), ?_, ?_, ?_⟩
  · rw [standardField_threes]
    exact retainQuota_e k η hη
  · rw [standardField_threes]
    exact V.chain η hη
  · intro a c ha hc
    have hdet : (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel.1 *
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse.2 -
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel.2 *
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse.1 ≠ 0 := by
      rw [frameAt_threes_child, kernel_threes, transverse_threes]
      have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
      intro h
      nlinarith
    refine FLatticePaper.Induction.rankWithIncrements_of_monotone_hull hdet hη
      (P := fun z => (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z)
      (J := fun z => (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η z)
      ?_ ?_ ?_ ?_ ?_ (hrank η hη) a c ha hc
    · intro z
      have h := (priceDrift_threes k z).1
      show (frameAt (List.replicate k Digit.three)).price (reciprocalField k)
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) =
        (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z - 1
      linarith
    · intro z
      have h := (priceDrift_threes k z).2
      show (frameAt (List.replicate k Digit.three)).price (reciprocalField k)
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) =
        (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z
      linarith
    · intro z
      have h := (slipDrift_threes k η z).1
      show (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) =
        (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η z
      unfold ChildFrame.roundedSlip
      congr 1
      linarith
    · intro z
      have h := (slipDrift_threes k η z).2
      show (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η
          (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) =
        (frameAt (List.replicate k Digit.three)).roundedSlip (reciprocalField k) η z + η
      unfold ChildFrame.roundedSlip
      omega
    · intro x y h
      have hp := V.price η hη x y h
      have hs := V.slip η hη x y h
      unfold slipPermits slipIncrement at hs
      have hsh : (reciprocalFrame k).shortShift = (frameAt (List.replicate k Digit.three)).shortShift := rfl
      rw [hsh] at hs
      dsimp only at hs
      unfold ChildFrame.roundedSlip ChildFrame.slip
      exact ⟨hp, by omega⟩

/-- **`StrongResidual` at `3^k` from the reciprocal values and the rank with increments.** -/
theorem strongResidual_threes_of_values (k : ℕ) (V : ReciprocalValues k)
    (hrank : ∀ η : ℤ, (η = 1 ∨ η = -1) →
      RankWithIncrements (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)))
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-1) η) :
    StrongResidual (List.replicate k Digit.three) :=
  FLatticePaper.Induction.strongResidual_threes_of_policy k (F2F3_threes_of_values k V hrank)

/-- **The headline's pure inputs at every `3^k`, modulo the reciprocal values and the rank with increments.**
`hpureSlip` is `baseSlip_threes` (unconditional); `hpureRes` is `strongResidual_threes_of_values`. -/
theorem pureInputs_threes (hV : ∀ k : ℕ, ReciprocalValues k)
    (hrank : ∀ k : ℕ, ∀ η : ℤ, (η = 1 ∨ η = -1) →
      RankWithIncrements (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)))
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel
        (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse (-1) η) :
    (∀ k : ℕ, FLatticePaper.Induction.BaseSlip (List.replicate k Digit.three)) ∧
      (∀ k : ℕ, FLatticePaper.Induction.StrongResidual (List.replicate k Digit.three)) :=
  ⟨fun k => FLatticePaper.Induction.baseSlip_threes k,
    fun k => strongResidual_threes_of_values k (hV k) (hrank k)⟩

end FLatticePaper.EPolicy
