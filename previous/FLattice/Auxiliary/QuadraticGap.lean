import FLattice.Auxiliary.PositiveQuadratic
import FLattice.Auxiliary.QuadraticSublevels

/-!
# Proper gaps above an affine quadratic reference

The reference is allowed an arbitrary affine part and a bounded error.
This is useful when a prescribed-value comparison is translated. The
unknown function has the literal uniform quadratic asymptotic expansion;
no periodicity, graph structure, or integrality is needed for this step.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.QuadraticGap

/-- A scalar linear form is bounded below by an arbitrarily small negative quadratic. -/
theorem linear_lower_bound (c a b x y : ℝ) (hc : 0 < c) :
    -(c / 8) * (x ^ 2 + y ^ 2) - 2 * (a ^ 2 + b ^ 2) / c ≤ -a * x - b * y := by
  have hCancel : c * (2 * (a ^ 2 + b ^ 2) / c) = 2 * (a ^ 2 + b ^ 2) := by
    field_simp
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith [sq_nonneg (c * x - 4 * a), sq_nonneg (c * y - 4 * b)]

/-- Strict matrix domination makes the gap above a bounded perturbation of an
affine quadratic reference proper on the integer plane. -/
theorem finite_sublevels
    (h u : ℤ × ℤ → ℝ) (M N : Matrix (Fin 2) (Fin 2) ℝ) (a b d B : ℝ)
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |h (x, y) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hReference : ∀ x y : ℤ,
      |u (x, y) - (-(1 / 2 : ℝ) *
          ((x : ℝ) * N 0 0 * (x : ℝ) + (x : ℝ) * N 0 1 * (y : ℝ) +
            (y : ℝ) * N 1 0 * (x : ℝ) + (y : ℝ) * N 1 1 * (y : ℝ)) +
        a * (x : ℝ) + b * (y : ℝ) + d)| ≤ B)
    (hPositive : (M + N).PosDef) (t : ℝ) :
    {z : ℤ × ℤ | h z - u z ≤ t}.Finite := by
  obtain ⟨c, hc, hQuadratic⟩ := exists_pos_quadratic_lower_bound (M + N) hPositive
  obtain ⟨R, _, hApprox⟩ := hGrowth (c / 4) (by positivity)
  let K := d + B + 2 * (a ^ 2 + b ^ 2) / c
  apply finite_sublevel_of_eventual_quadratic_lower_bound
    (fun z => h z - u z) (c / 8) K (R ^ 2) (by positivity) ?_ t
  rintro ⟨x, y⟩ hSize
  have hGrowthLower := (abs_le.mp (hApprox x y hSize)).1
  have hErrorUpper := (abs_le.mp (hReference x y)).2
  have hQuad := hQuadratic (x : ℝ) (y : ℝ)
  simp only [Matrix.add_apply] at hQuad
  have hLinear := linear_lower_bound c a b (x : ℝ) (y : ℝ) hc
  dsimp [K]
  nlinarith

end FLattice.Auxiliary.QuadraticGap
