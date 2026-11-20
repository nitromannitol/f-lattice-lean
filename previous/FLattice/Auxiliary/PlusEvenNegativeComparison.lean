import FLattice.Auxiliary.PlusEvenNegativeShift
import FLattice.Auxiliary.PlusEvenNegativeValues

/-!
# Negative prescribed-coset comparison from the original growth assumptions

The translated profile comparison supplies every literal incoming collar
bound of the finite triangle. The global parabola then raises its gap and
forces the target value. The unknown function has no periodicity hypothesis.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

open NegativeTriangle

/-- The negative prescribed coset forces the origin bound under the source
quadratic growth and strict matrix domination. The full triangle is raised
at the same time; every collar bound is derived from the explicit profile. -/
theorem triangle_and_origin_of_negative_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          1 - 2 * m.val * a - 2 * b)) :
    (∀ z ∈ region m.val, baseline z.2 + 2 ≤ h z) ∧ 1 ≤ h (0, 0) := by
  obtain ⟨hOne, hTwo⟩ := negative_shift_comparison_of_quadratic_growth
    m h M hSuperharmonic hGrowth hPositive hPrescribed
  apply triangle_and_origin_lower_bound m.val m.property h hSuperharmonic
  · intro x y hz
    obtain ⟨hx, hxm, hy, hyx, hsum⟩ := hz
    have hBound := hOne x y
      (negative_shift_triangle_not_prescribed m x y hx hxm hy hyx)
    rw [negative_shift_triangle m x y hx hxm hy hyx hsum] at hBound
    split_ifs at hBound <;> omega
  · intro i hi him
    by_cases hi0 : i = 0
    · subst i
      have hBound := hTwo 0 1 (negative_shift_left_zero_regionI m)
      rw [negative_shift_left_zero] at hBound
      norm_num only [zero_add, baseline, Int.reduceSub, Int.reduceMul,
        Int.reduceDiv, Int.reduceNeg, Int.reduceAdd] at hBound ⊢
      exact hBound
    · have hi1 : 1 ≤ i := by omega
      have hBound := hOne i (i + 1)
        (negative_shift_left_boundary_not_prescribed m i hi1 him)
      rwa [negative_shift_left_boundary m i hi1 him] at hBound
  · intro i hi him
    have hBound := hOne i (2 * m.val + 2 - i)
      (negative_shift_right_boundary_not_prescribed m i hi him)
    rw [negative_shift_right_boundary m i hi him] at hBound
    omega
  · intro i hi him hOdd
    by_cases hi1 : i = 1
    · have hBound := hOne i (-1) (negative_shift_odd_not_prescribed m i (-1) hOdd)
      rw [negative_shift_bottom_boundary m i hi him hOdd, if_pos hi1] at hBound
      omega
    · have hBound := hTwo i (-1)
        (negative_shift_bottom_regionI m i (by omega) him hOdd)
      rw [negative_shift_bottom_boundary m i hi him hOdd, if_neg hi1] at hBound
      omega
  · simpa only [Int.pow_zero, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)]
      using hPrescribed 0 0
  · have hBound := hOne (-1) 0 (negative_shift_odd_not_prescribed m (-1) 0 (by decide))
    rw [negative_shift_left_of_origin] at hBound
    omega

end FLattice.Auxiliary.PlusEvenProfile
