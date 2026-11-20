import FLattice.Auxiliary.PlusEvenMatrix
import FLattice.Auxiliary.PlusEvenComparison
import FLattice.Auxiliary.PositiveQuadratic
import FLattice.Auxiliary.QuadraticSublevels

/-!
# Even-plus comparison under the source quadratic-growth assumptions

The growth premise is the uniform epsilon definition at lattice infinity,
with radius squared and the literal one-half matrix quadratic. Strict
domination is positive definiteness of M plus the actual inverse of C.
Coercivity, bounded profile error, and finite gap sublevels are derived.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- Exact quadratic growth above the source matrix makes every integer gap sublevel finite. -/
theorem finite_gap_sublevels_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) :
    ∀ b : ℤ, {z : ℤ × ℤ | h z - profile m z.1 z.2 ≤ b}.Finite := by
  obtain ⟨c, hc, hQuadratic⟩ :=
    exists_pos_quadratic_lower_bound (M + (periodMatrix m)⁻¹) hPositive
  obtain ⟨B, _, hBound⟩ := exists_bound_profile_sub_quadraticBackground m
  obtain ⟨R, _, hApprox⟩ := hGrowth (c / 4) (by positivity)
  let K : ℝ := 3 / 4 + (m.val : ℝ) ^ 2 / (4 * (halfPeriod m : ℝ)) + B + 1 / (2 * c)
  have hLower : ∀ z : ℤ × ℤ, R ^ 2 ≤ (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 →
      (c / 8) * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) - K ≤
        (h z : ℝ) - (profile m z.1 z.2 : ℝ) := by
    rintro ⟨x, y⟩ hSize
    have hGrowthLower := (abs_le.mp (hApprox x y hSize)).1
    have hErrorUpper := (abs_le.mp (hBound x y)).2
    have hQuad := hQuadratic (x : ℝ) (y : ℝ)
    simp only [Matrix.add_apply] at hQuad
    have hBackground := quadraticBackground_eq_inverse m x y
    have hYoung : -(c / 8) * (y : ℝ) ^ 2 - 1 / (2 * c) ≤ (y : ℝ) / 2 := by
      have hCancel : c * (1 / (2 * c)) = (1 / 2 : ℝ) := by
        field_simp
      apply (mul_le_mul_iff_right₀ hc).mp
      nlinarith [sq_nonneg (c * (y : ℝ) + 2)]
    dsimp [K]
    nlinarith [sq_nonneg (x : ℝ)]
  intro b
  have hFinite := finite_sublevel_of_eventual_quadratic_lower_bound
    (fun z : ℤ × ℤ => (h z : ℝ) - (profile m z.1 z.2 : ℝ))
    (c / 8) K (R ^ 2) (by positivity) hLower (b : ℝ)
  apply hFinite.subset
  intro z hz
  change (h z : ℝ) - (profile m z.1 z.2 : ℝ) ≤ (b : ℝ)
  exact_mod_cast hz

/-- The complete comparison gains under literal quadratic growth and strict matrix domination. -/
theorem profile_comparison_of_quadratic_growth
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
        h (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -1 - 2 * m.val * a - 2 * b)) :
    (∀ z : ℤ × ℤ, ¬cellPrescribed (cellOf m z.1 z.2) →
      profile m z.1 z.2 + 1 ≤ h z) ∧
    (∀ z : ℤ × ℤ, regionI (cellOf m z.1 z.2) → profile m z.1 z.2 + 2 ≤ h z) := by
  exact profile_comparison_of_finite_sublevels m h hSuperharmonic hPrescribed
    (finite_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive)

/-- The origin bound under the manuscript's quadratic-growth and pin hypotheses. -/
theorem one_le_origin_of_quadratic_growth
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
        h (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -1 - 2 * m.val * a - 2 * b)) :
    1 ≤ h (0, 0) := by
  exact one_le_origin_of_finite_sublevels m h hSuperharmonic hPrescribed
    (finite_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive)

end FLattice.Auxiliary.PlusEvenProfile
