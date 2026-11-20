import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The smallest-plus matrix and the quadratic backgrounds of its two profiles

Both parities use the literal matrix C = [[6,2],[2,2]]. The affine part of
the background records the parity-dependent diagonal-period increment.
Arbitrary translations keep the same quadratic matrix, with exact affine
coefficients for later growth comparisons.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- The real period matrix in the smallest-plus transport. -/
noncomputable def periodMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![6, 2; 2, 2]

/-- The actual matrix inverse agrees with the displayed source inverse. -/
theorem periodMatrix_inv : periodMatrix⁻¹ = !![(1 : ℝ) / 4, -1 / 4; -1 / 4, 3 / 4] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [periodMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The source affine period increments determine this quadratic background. -/
noncomputable def quadraticBackground (ε : Fin 2) (x y : ℤ) : ℝ :=
  -((x : ℝ) - (y : ℝ)) ^ 2 / 8 - (y : ℝ) ^ 2 / 4 -
    (1 - (ε.val : ℝ)) * (y : ℝ) / 2

/-- The background has precisely the signed affine increments of the profile. -/
theorem quadraticBackground_at_lift (ε : Fin 2) (x y k q : ℤ) :
    quadraticBackground ε (x + 2 * k + 4 * q) (2 * k + y) =
      quadraticBackground ε x y - (q : ℝ) * (x : ℝ) + (q : ℝ) * (y : ℝ) -
        2 * (q : ℝ) ^ 2 - (k : ℝ) * (y : ℝ) - (k : ℝ) ^ 2 -
        (1 - (ε.val : ℝ)) * (k : ℝ) := by
  unfold quadraticBackground
  push_cast
  ring

/-- Every integer translation retains minus the actual inverse as quadratic
matrix; all remaining coefficients are explicit affine terms. -/
theorem quadraticBackground_shift_eq_inverse (ε : Fin 2) (x y a b : ℤ) :
    quadraticBackground ε (x + a) (y + b) = -(1 / 2 : ℝ) *
      ((x : ℝ) * (periodMatrix⁻¹ 0 0) * (x : ℝ) +
        (x : ℝ) * (periodMatrix⁻¹ 0 1) * (y : ℝ) +
        (y : ℝ) * (periodMatrix⁻¹ 1 0) * (x : ℝ) +
        (y : ℝ) * (periodMatrix⁻¹ 1 1) * (y : ℝ)) +
      (((b : ℝ) - (a : ℝ)) / 4) * (x : ℝ) +
      (((a : ℝ) - 3 * (b : ℝ)) / 4 - (1 - (ε.val : ℝ)) / 2) * (y : ℝ) +
      (-((a : ℝ) - (b : ℝ)) ^ 2 / 8 - (b : ℝ) ^ 2 / 4 -
        (1 - (ε.val : ℝ)) * (b : ℝ) / 2) := by
  rw [periodMatrix_inv]
  norm_num [quadraticBackground]
  ring

end FLattice.Auxiliary.MiddleProfile
