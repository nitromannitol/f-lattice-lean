import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-!
# Uniform lower bounds for real positive-definite two-by-two matrices

The hypothesis is the literal Mathlib `Matrix.PosDef`. Symmetry and the
positive determinant are derived from it. The lower-bound constant is the
determinant divided by the trace; the proof is an elementary sum of squares.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

/-- Expand the actual matrix quadratic form on a real two-vector. -/
theorem quadratic_two_expansion (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    star (![x, y] : Fin 2 → ℝ) ⬝ᵥ A.mulVec ![x, y] =
      x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x + y * A 1 1 * y := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Literal positive definiteness supplies one positive quadratic lower
bound valid uniformly for all real coordinates. -/
theorem exists_pos_quadratic_lower_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ,
      c * (x ^ 2 + y ^ 2) ≤
        x * A 0 0 * x + x * A 0 1 * y + y * A 1 0 * x + y * A 1 1 * y := by
  let a := A 0 0
  let b := A 0 1
  let d := A 1 1
  have ha : 0 < a := hA.diag_pos
  have hd : 0 < d := hA.diag_pos
  have hSym : A 1 0 = b := by
    simpa only [star_trivial] using hA.isHermitian.apply 0 1
  have hVector : (![ -b, a] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h1 := congr_fun h 1
    have hZero : a = 0 := by simpa using h1
    exact (ne_of_gt ha) hZero
  have hTest := hA.dotProduct_mulVec_pos hVector
  rw [quadratic_two_expansion, hSym] at hTest
  change 0 < -b * a * -b + -b * b * a + a * b * -b + a * d * a at hTest
  have hDet : 0 < a * d - b ^ 2 := by
    have hProduct : 0 < a * (a * d - b ^ 2) := by nlinarith only [hTest]
    exact (mul_pos_iff_of_pos_left ha).mp hProduct
  have hTrace : 0 < a + d := add_pos ha hd
  refine ⟨(a * d - b ^ 2) / (a + d), div_pos hDet hTrace, ?_⟩
  intro x y
  rw [hSym]
  change (a * d - b ^ 2) / (a + d) * (x ^ 2 + y ^ 2) ≤
    x * a * x + x * b * y + y * b * x + y * d * y
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hTrace).mpr
  nlinarith only [sq_nonneg (a * x + b * y), sq_nonneg (b * x + d * y)]

end FLattice.Auxiliary
