import FLattice.Auxiliary.PlusEvenQuadratic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# The actual period matrix and the quadratic background

The matrix below is the source's real matrix C. Its inverse is the ordinary
matrix inverse, identified by an explicit multiplication. The background's
quadratic part is exactly minus one half of that inverse quadratic form.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The real period matrix C in the even-plus comparison statement. -/
noncomputable def periodMatrix (m : Parameter) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4 * (m.val : ℝ) ^ 2 + 4 * (m.val : ℝ) - 2, 2 * (m.val : ℝ);
    2 * (m.val : ℝ), 2]

/-- The determinant is the positive quotient size 4J. -/
theorem periodMatrix_det (m : Parameter) :
    (periodMatrix m).det = 4 * (halfPeriod m : ℝ) := by
  rw [periodMatrix, Matrix.det_fin_two_of]
  unfold halfPeriod
  push_cast
  ring

/-- The source inverse is the actual inverse of C for every allowed parameter. -/
theorem periodMatrix_inv (m : Parameter) :
    (periodMatrix m)⁻¹ =
      !![2 / (4 * (halfPeriod m : ℝ)),
        (-2 * (m.val : ℝ)) / (4 * (halfPeriod m : ℝ));
        (-2 * (m.val : ℝ)) / (4 * (halfPeriod m : ℝ)),
        (4 * (m.val : ℝ) ^ 2 + 4 * (m.val : ℝ) - 2) / (4 * (halfPeriod m : ℝ))] := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> unfold halfPeriod <;> push_cast <;> ring

/-- The polynomial has quadratic matrix minus C inverse, with its precise affine part. -/
theorem quadraticBackground_eq_inverse (m : Parameter) (x y : ℤ) :
    quadraticBackground m x y =
      -(1 / 2 : ℝ) *
        ((x : ℝ) * ((periodMatrix m)⁻¹ 0 0) * (x : ℝ) +
          (x : ℝ) * ((periodMatrix m)⁻¹ 0 1) * (y : ℝ) +
          (y : ℝ) * ((periodMatrix m)⁻¹ 1 0) * (x : ℝ) +
          (y : ℝ) * ((periodMatrix m)⁻¹ 1 1) * (y : ℝ)) -
        (y : ℝ) / 2 + 3 / 4 + (m.val : ℝ) ^ 2 / (4 * (halfPeriod m : ℝ)) := by
  have hJ : (halfPeriod m : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (halfPeriod_pos m)
  rw [periodMatrix_inv]
  norm_num [quadraticBackground]
  field_simp
  unfold halfPeriod
  push_cast
  ring

end FLattice.Auxiliary.PlusEvenProfile
