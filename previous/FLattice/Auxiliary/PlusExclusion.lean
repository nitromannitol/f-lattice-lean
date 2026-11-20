import FLattice.Auxiliary.PlusEvenGrowth
import FLattice.Auxiliary.PlusEvenNegativeComparison
import FLattice.Auxiliary.PlusOddContactEscape

/-!
# Excluding normalized failed stars for the general plus coefficient

The two signed prescribed-coset bounds cover every integer threshold.
The four proved root comparisons handle the two signs and native parities.
This assembly requires only original quadratic growth, native
superharmonicity, actual inverse-matrix positivity and the literal coset
bounds; no profile, geometric, contact-finiteness or periodicity premise is
exported. The smallest coefficient is treated separately.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusExclusion

open PlusEvenProfile

/-- The literal two signed coset bounds cannot accompany a normalized
failed star under original growth and strict inverse-matrix domination. -/
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
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) -
        (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (c * (if ε = 0 then -2 * m.val else -1) -
            (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          c * (if ε = 0 then -1 else 0) - 2 * m.val * a - 2 * b)) : False := by
  by_cases hThreshold : 1 ≤ τ
  · have hUnitPins : ∀ a b : ℤ,
        1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
          h ((if ε = 0 then -2 * m.val else -1) -
              (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            (if ε = 0 then -1 else 0) - 2 * m.val * a - 2 * b) := by
      intro a b
      have hBound := hPins 1 (Or.inr rfl) a b
      norm_num only [one_mul, if_neg (by decide : (1 : ℤ) ≠ -1), add_zero] at hBound
      omega
    fin_cases ε
    · have hSH : ∀ x y : ℤ,
          (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
            else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
        simpa using hSuperharmonic
      have hRoot := PlusEvenProfile.one_le_origin_of_quadratic_growth m h M
        hSH hGrowth hPositive (by simpa using hUnitPins)
      omega
    · have hSH : ∀ x y : ℤ,
          (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
            else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
        simpa using hSuperharmonic
      have hRoot := PlusOddProfile.one_le_origin_of_quadratic_growth m h M
        hSH hGrowth hPositive (by simpa using hUnitPins)
      omega
  · have hUnitPins : ∀ a b : ℤ,
        1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
          h (-(if ε = 0 then -2 * m.val else -1) -
              (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
            -(if ε = 0 then -1 else 0) - 2 * m.val * a - 2 * b) := by
      intro a b
      have hBound := hPins (-1) (Or.inl rfl) a b
      simp only [neg_one_mul, if_true] at hBound
      omega
    fin_cases ε
    · have hSH : ∀ x y : ℤ,
          (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
            else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
        simpa using hSuperharmonic
      have hRoot := (PlusEvenProfile.triangle_and_origin_of_negative_quadratic_growth
        m h M hSH hGrowth hPositive (by simpa using hUnitPins)).2
      omega
    · have hSH : ∀ x y : ℤ,
          (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
            else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
        simpa using hSuperharmonic
      have hRoot := PlusOddProfile.one_le_origin_of_negative_quadratic_growth m h M
        hSH hGrowth hPositive (by simpa using hUnitPins)
      omega

end FLattice.Auxiliary.PlusExclusion
