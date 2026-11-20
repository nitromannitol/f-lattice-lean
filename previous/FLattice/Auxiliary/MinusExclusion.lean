import FLattice.Auxiliary.MinusShiftComparison
import FLattice.Auxiliary.MinusZeroValues

/-!
# Excluding normalized general-minus failed stars

The two signed cosets exclude every odd threshold and reduce the even case
to threshold zero. The central coset then supplies the shifted odd profile;
the proved fourteen-value calculation closes that final case. All growth,
parity and shifted comparisons are derived from the original hypotheses.
This module concerns m>=2, not the separately treated coefficient four.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusExclusion

open PlusEvenProfile MinusProfile

/-- No normalized failed star has the three original coset bounds together
with native SH, quadratic growth and actual inverse-matrix positivity. -/
theorem not_normalized_failed_star_of_quadratic_growth
    (m : Parameter) (ε : Fin 2) (h : ℤ × ℤ → ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hOrigin : h (0, 0) = 0)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 0 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (c * (if ε = 0 then 2 * m.val + 2 else -1) -
            (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          c * (if ε = 0 then 1 else 0) - 2 * m.val * a - 2 * b)) : False := by
  have hSigned : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
        h (c * (if ε = 0 then 2 * m.val + 2 else -1) -
            (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          c * (if ε = 0 then 1 else 0) - 2 * m.val * a - 2 * b) := by
    intro c hc
    exact hPins c (hc.elim Or.inl (fun hOne => Or.inr (Or.inr hOne)))
  fin_cases ε
  · have hSH : ∀ x y : ℤ,
        (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
          else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
      simpa using hSuperharmonic
    have hTau := even_threshold_eq_zero m h M τ hSH hGrowth hPositive
      (by simpa using hSigned) hOrigin
    subst τ
    obtain ⟨hC, hA⟩ := even_signed_shift_bounds m h M 0 hSH hGrowth hPositive
      (by simpa using hSigned)
    have hCentral : ∀ a b : ℤ,
        -(halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) ≤
          h (-(4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            -2 * m.val * a - 2 * b) := by
      intro a b
      simpa only [zero_mul, if_neg (by decide : (0 : ℤ) ≠ -1), zero_add, zero_sub, neg_mul] using
        hPins 0 (Or.inr (Or.inl rfl)) a b
    have hB := even_central_coset_odd_lower_bound m h M hSH hGrowth hPositive hCentral
    have hRoot := one_le_origin_of_three_profiles m h hSH (by omega)
      (by simpa only [sub_zero, add_assoc] using hA) hB (by simpa only [add_zero] using hC)
    omega
  · have hSH : ∀ x y : ℤ,
        (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
          else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
      simpa using hSuperharmonic
    exact odd_signed_cosets_exclude_zero_origin m h M τ hSH hGrowth hPositive
      (by simpa using hSigned) hOrigin

end FLattice.Auxiliary.MinusExclusion
