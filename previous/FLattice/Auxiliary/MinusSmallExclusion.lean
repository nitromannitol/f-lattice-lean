import FLattice.Auxiliary.MinusSmallShiftComparison
import FLattice.Auxiliary.MinusSmallZeroValues
import FLattice.Auxiliary.MiddleMatrix

/-!
# The complete smallest-minus normalized failed-star exclusion

Every shifted comparison and every initial averaging value is derived from
the original three signed coset bounds. The final theorem retains only the
source native SH, quadratic growth, actual inverse positivity and root
normalization. It covers all integer thresholds and both native parities.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallExclusion

open MinusSmallProfile

/-- No smallest-minus normalized failed star satisfies the original hypotheses. -/
theorem not_normalized_failed_star_of_quadratic_growth
    (ε : Fin 2) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + MiddleProfile.periodMatrix⁻¹).PosDef)
    (hOrigin : h (0, 0) = 0)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 0 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (3 * a ^ 2 + 2 * a * b + b ^ 2 - 2 * a - b) ≤
        h (c * (if ε = 0 then 4 else -1) - 6 * a - 2 * b,
          c * (if ε = 0 then 1 else 0) - 2 * a - 2 * b)) : False := by
  have hPos : (M + MinusSmallProfile.periodMatrix⁻¹).PosDef := hPositive
  have hSigned : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) - cost a b ≤
        h (c * prescribedX ε - 6 * a - 2 * b,
          c * prescribedY ε - 2 * a - 2 * b) := by
    intro c hc
    exact hPins c (hc.elim Or.inl (fun hOne => Or.inr (Or.inr hOne)))
  obtain ⟨hPlus, hMinus⟩ := signed_shift_bounds ε h M τ hSuperharmonic hGrowth hPos hSigned
  have hCases := threshold_cases_of_shift_bounds ε h τ hOrigin hPlus hMinus
  fin_cases ε
  · have hSH : ∀ x y : ℤ,
        (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
          else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
      simpa using hSuperharmonic
    norm_num [prescribedX, prescribedY, Fin.ext_iff] at hPlus hMinus hCases
    have hCentral : ∀ a b : ℤ, -cost a b ≤ h (-6 * a - 2 * b, -2 * a - 2 * b) := by
      intro a b
      simpa only [cost, zero_mul, if_neg (by decide : (0 : ℤ) ≠ -1), zero_add, zero_sub,
        neg_mul] using hPins 0 (Or.inr (Or.inl rfl)) a b
    have hB := even_central_coset_odd_lower_bound h M hSH hGrowth hPos hCentral
    rcases hCases with rfl | rfl | rfl
    · have hRoot := one_le_origin_of_even_minus_two_profiles h hSH
        (by intro x y; have hb := hMinus x y; omega) hB
      omega
    · have hRoot := one_le_origin_of_even_minus_one_profiles h hSH
        (by intro x y; have hb := hMinus x y; omega) hB
        (by intro x y; have hb := hPlus x y; omega)
      omega
    · have hRoot := one_le_origin_of_three_profiles h hSH (by omega)
        (by intro x y; have hb := hMinus x y; omega) hB
        (by intro x y; have hb := hPlus x y; omega)
      omega
  · have hSH : ∀ x y : ℤ,
        (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
          else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
      simpa using hSuperharmonic
    norm_num [prescribedX, prescribedY, Fin.ext_iff] at hPlus hMinus hCases
    subst τ
    have hRoot := one_le_origin_of_odd_one_profiles h hSH
      (by intro x y; have hb := hPlus x y; omega)
      (by intro x y; have hb := hMinus x y; simp only [sub_eq_add_neg]; omega)
    omega

end FLattice.Auxiliary.MinusSmallExclusion
