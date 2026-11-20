import FLattice.Auxiliary.MiddleNegativeShift
import FLattice.Auxiliary.MiddleNegativePrefix
import FLattice.Auxiliary.MiddleContactPaths

/-!
# Excluding the normalized failed star at the smallest plus coefficient

Both native parities and every integer threshold are covered. For positive
threshold, the unshifted comparison and its white path suffice. For a
nonpositive threshold, the negative comparison and both original pin
families force contact at the shifted repeating path, a contradiction.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- No normalized failed star satisfies the original two signed coset
bounds, native superharmonicity, quadratic growth and strict matrix domination. -/
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
    (hPositive : (M + periodMatrix⁻¹).PosDef)
    (hOrigin : h (0, 0) = 0)
    (hPins : ∀ c : ℤ, c = -1 ∨ c = 1 → ∀ a b : ℤ,
      c * τ + (if c = -1 then 1 else 0) - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
        h (c * (-2 + (ε.val : ℤ)) - 6 * a - 2 * b,
          c * (-1 + (ε.val : ℤ)) - 2 * a - 2 * b)) : False := by
  have hPositivePins : ∀ a b : ℤ,
      τ - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
        h (-2 + (ε.val : ℤ) - 6 * a - 2 * b, -1 + (ε.val : ℤ) - 2 * a - 2 * b) := by
    intro a b
    simpa using hPins 1 (Or.inr rfl) a b
  have hNegativePins : ∀ a b : ℤ,
      1 - τ - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
        h (2 - (ε.val : ℤ) - 6 * a - 2 * b, 1 - (ε.val : ℤ) - 2 * a - 2 * b) := by
    intro a b
    have hBound := hPins (-1) (Or.inl rfl) a b
    norm_num at hBound
    rw [show -(ε.val : ℤ) + 2 = 2 - (ε.val : ℤ) by ring,
      show -(ε.val : ℤ) + 1 = 1 - (ε.val : ℤ) by ring] at hBound
    omega
  by_cases hThreshold : 1 ≤ τ
  · have hUnitPins : ∀ a b : ℤ,
        1 - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
          h (-2 + (ε.val : ℤ) - 6 * a - 2 * b, -1 + (ε.val : ℤ) - 2 * a - 2 * b) := by
      intro a b
      have hBound := hPositivePins a b
      omega
    have hLower := profile_le_of_quadratic_growth ε h M hSuperharmonic hGrowth hPositive hUnitPins
    have hFinite := finite_shifted_gap_sublevels_of_quadratic_growth ε 0 0 h M hGrowth hPositive 0
    have hContacts : {z : ℤ × ℤ | h z = profile ε z.1 z.2}.Finite := by
      apply hFinite.subset
      intro z hz
      change h z - profile ε (z.1 + 0) (z.2 + 0) ≤ 0
      change h z = profile ε z.1 z.2 at hz
      rw [add_zero, add_zero, hz, sub_self]
    have hStrict := positive_cycle_start_lt_of_finite_contacts ε h hSuperharmonic hLower hContacts
    omega
  · have hThresholdNonpositive : τ ≤ 0 := by omega
    have hUnitPins : ∀ a b : ℤ,
        1 - (3 * a ^ 2 + 2 * a * b + b ^ 2 + a) ≤
          h (2 - (ε.val : ℤ) - 6 * a - 2 * b, 1 - (ε.val : ℤ) - 2 * a - 2 * b) := by
      intro a b
      have hBound := hNegativePins a b
      omega
    have hLower := negative_shift_comparison_of_quadratic_growth ε h M
      hSuperharmonic hGrowth hPositive hUnitPins
    have hFinite := finite_shifted_gap_sublevels_of_quadratic_growth ε
      (2 * (-2 + (ε.val : ℤ))) (2 * (-1 + (ε.val : ℤ))) h M hGrowth hPositive 0
    have hContacts : {z : ℤ × ℤ | h z =
        profile ε (z.1 + 2 * (-2 + (ε.val : ℤ))) (z.2 + 2 * (-1 + (ε.val : ℤ)))}.Finite := by
      apply hFinite.subset
      intro z hz
      change h z - profile ε (z.1 + 2 * (-2 + (ε.val : ℤ)))
        (z.2 + 2 * (-1 + (ε.val : ℤ))) ≤ 0
      rw [hz, sub_self]
    fin_cases ε
    · have hEvenSH : ∀ x y : ℤ,
          (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
            else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
        simpa using hSuperharmonic
      have hEvenLower : ∀ z : ℤ × ℤ, profile 0 (z.1 - 4) (z.2 - 2) ≤ h z := by
        intro z
        simpa [sub_eq_add_neg] using hLower z.1 z.2
      have hEvenContacts : {z : ℤ × ℤ | h z = profile 0 (z.1 - 4) (z.2 - 2)}.Finite := by
        simpa [sub_eq_add_neg] using hContacts
      have hContact := negative_even_cycle_contact h τ hEvenSH hOrigin
        (by simpa using hPositivePins) (by simpa using hNegativePins) hEvenLower
      have hStrict := negative_even_cycle_start_lt_of_finite_contacts h hEvenSH hEvenLower hEvenContacts
      omega
    · have hOddSH : ∀ x y : ℤ,
          (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
            else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y) := by
        simpa using hSuperharmonic
      have hOddLower : ∀ z : ℤ × ℤ, profile 1 (z.1 - 2) z.2 ≤ h z := by
        intro z
        simpa [sub_eq_add_neg] using hLower z.1 z.2
      have hOddContacts : {z : ℤ × ℤ | h z = profile 1 (z.1 - 2) z.2}.Finite := by
        simpa [sub_eq_add_neg] using hContacts
      have hContact := negative_odd_cycle_contact h τ hOddSH hOrigin
        (by simpa using hPositivePins) (by simpa using hNegativePins) hOddLower
      have hStrict := negative_odd_cycle_start_lt_of_finite_contacts h hOddSH hOddLower hOddContacts
      omega

end FLattice.Auxiliary.MiddleProfile
