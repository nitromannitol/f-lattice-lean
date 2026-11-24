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

/-- **The hull lemma from any strict deck-equivariant rank.** Let `R` be strict on the retained edges, with characters `cU, cV`
on the periods. Let `L = |cU| + |cV| + 1`. For positive `a, b`, the rank `Q = (aL + cU) P + (bL − η cV) J + R` has increments
`(−a L, b η L)` and is strict on the retained edges, since both coefficients are nonnegative and `P, J` are nonincreasing. -/
theorem rankWithIncrements_of_strict_hull {retained : Site → Site → Prop} {U V : Site} {η : ℤ}
    (hη : η = 1 ∨ η = -1) {P J R : Site → ℤ} {cU cV : ℤ}
    (hPU : ∀ z, P (z + U) = P z - 1) (hPV : ∀ z, P (z + V) = P z)
    (hJU : ∀ z, J (z + U) = J z) (hJV : ∀ z, J (z + V) = J z + η)
    (hmono : ∀ x y, retained x y → P y ≤ P x ∧ J y ≤ J x)
    (hRU : ∀ z, R (z + U) = R z + cU) (hRV : ∀ z, R (z + V) = R z + cV)
    (hstrict : ∀ x i, retained x i → R i < R x)
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    RankWithIncrements retained U V (-a) (b * η) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℤ, L = |cU| + |cV| + 1 := ⟨_, rfl⟩
  have hL : 1 ≤ L := by linarith [abs_nonneg cU, abs_nonneg cV]
  have ha1 : 1 ≤ a := ha
  have hb1 : 1 ≤ b := hb
  have hcU : -|cU| ≤ cU := neg_abs_le cU
  have hηcV : η * cV ≤ |cV| := by
    rcases hη with rfl | rfl
    · simpa using le_abs_self cV
    · simpa using neg_le_abs cV
  have hη2 : η * η = 1 := by rcases hη with rfl | rfl <;> norm_num
  have haL : L ≤ a * L := by nlinarith
  have hbL : L ≤ b * L := by nlinarith
  have hα : 0 ≤ a * L + cU := by linarith [abs_nonneg cV]
  have hβ : 0 ≤ b * L - η * cV := by linarith [abs_nonneg cU]
  unfold RankWithIncrements
  refine ⟨fun z => (a * L + cU) * P z + (b * L - η * cV) * J z + R z, L, by linarith, ?_, ?_, ?_⟩
  · intro x i hr
    obtain ⟨hp, hj⟩ := hmono x i hr
    have h1 := mul_le_mul_of_nonneg_left hp hα
    have h2 := mul_le_mul_of_nonneg_left hj hβ
    have h3 := hstrict x i hr
    dsimp only
    linarith
  · intro z
    dsimp only
    rw [hPU, hJU, hRU]
    ring
  · intro z
    dsimp only
    rw [hPV, hJV, hRV]
    linear_combination (-cV) * hη2

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
