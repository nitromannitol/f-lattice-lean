import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NoncommRing

/-!
# Strict inverse order and the transport matrix map

A direct positive-definite plus positive-semidefinite decomposition proves
strict order reversal of actual matrix inverses. Congruence then proves
strict order preservation of the transport matrix formula. No inverse-order
inequality is assumed, and no claim about asymptotic growth is made here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MatrixInverseOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual inverses strictly reverse positive-definite order. -/
theorem inv_sub_inv_posDef (A B : Matrix n n ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hDifference : (A - B).PosDef) :
    (B⁻¹ - A⁻¹).PosDef := by
  letI := hA.isUnit.invertible
  letI := hB.isUnit.invertible
  have hStrict := hDifference.conjTranspose_mul_mul_same
    (B := A⁻¹) (Matrix.mulVec_injective_of_isUnit hA.inv.isUnit)
  have hNonnegative := hB.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  rw [hA.inv.isHermitian.eq] at hStrict
  rw [(hA.inv.isHermitian.sub hB.inv.isHermitian).eq] at hNonnegative
  have hIdentity : A⁻¹ * (A - B) * A⁻¹ +
      (A⁻¹ - B⁻¹) * B * (A⁻¹ - B⁻¹) = B⁻¹ - A⁻¹ := by
    noncomm_ring [Matrix.mul_inv_of_invertible, Matrix.inv_mul_cancel_left_of_invertible]
  rw [← hIdentity]
  exact hStrict.add_posSemidef hNonnegative

/-- The literal congruence formula for the transported quadratic matrix. -/
noncomputable def transportMatrix (R B M : Matrix n n ℝ) : Matrix n n ℝ :=
  B.transpose * (R - R * (M + R)⁻¹ * R) * B

/-- Strict positive-definite differences are preserved on the inverse
formula's domain; positivity of the larger argument is derived. -/
theorem transportMatrix_sub_posDef (R B M N : Matrix n n ℝ)
    (hR : R.IsSymm) (hRUnit : IsUnit R) (hBUnit : IsUnit B)
    (hBase : (N + R).PosDef) (hDifference : (M - N).PosDef) :
    (transportMatrix R B M - transportMatrix R B N).PosDef := by
  have hLarger : (M + R).PosDef := by
    convert hBase.add hDifference using 1
    noncomm_ring
  have hInverse := inv_sub_inv_posDef (M + R) (N + R) hLarger hBase
    (by simpa only [add_sub_add_right_eq_sub] using hDifference)
  have hInner := hInverse.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hRUnit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hR] at hInner
  have hOuter := hInner.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hBUnit)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hOuter
  convert hOuter using 1
  unfold transportMatrix
  noncomm_ring

end FLattice.Auxiliary.MatrixInverseOrder
