import FLattice.Auxiliary.QuadraticGrowthTranslation
import FLattice.Auxiliary.LatticeQuadraticRounding
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# The affine quarter-turn in the elementary F-lattice duality

The map (-y,x-1) interchanges the actual incoming axes and reverses native
parity, so its pullback preserves integer superharmonicity. Its linear part
is the literal quarter-turn P, and the original uniform growth transforms
to Pᵀ M P without a symmetry assumption on M. Harmonic addition is separate.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ElementaryDuality

/-- The exact physical affine rotation from the source. -/
def affineRotation (z : ℤ × ℤ) : ℤ × ℤ := (-z.2, z.1 - 1)

/-- The real linear part of the affine rotation. -/
noncomputable def rotationMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The quarter-turn is a unit, so it preserves strict matrix differences. -/
theorem rotationMatrix_isUnit : IsUnit rotationMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  norm_num [rotationMatrix, Matrix.det_fin_two_of]

/-- The two incoming sums agree exactly under the physical affine rotation. -/
theorem affineRotation_incoming_sum (f : ℤ × ℤ → ℤ) (x y : ℤ) :
    (if (x + y) % 2 = 0 then f (affineRotation (x - 1, y)) + f (affineRotation (x + 1, y))
      else f (affineRotation (x, y - 1)) + f (affineRotation (x, y + 1))) =
    (if (-y + (x - 1)) % 2 = 0 then f (-y - 1, x - 1) + f (-y + 1, x - 1)
      else f (-y, x - 1 - 1) + f (-y, x - 1 + 1)) := by
  by_cases he : (x + y) % 2 = 0
  · have ho : (-y + (x - 1)) % 2 ≠ 0 := by omega
    simp only [he, ho, if_true, if_false, affineRotation, add_sub_cancel_right, sub_add_cancel]
  · have ho : (-y + (x - 1)) % 2 = 0 := by omega
    simp only [he, ho, if_true, if_false, affineRotation]
    rw [show -(y - 1) = -y + 1 by omega, show -(y + 1) = -y - 1 by omega]
    exact add_comm _ _

/-- Pullback by the exact affine rotation preserves native integer SH. -/
theorem affineRotation_superharmonic (f : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then f (x - 1, y) + f (x + 1, y)
        else f (x, y - 1) + f (x, y + 1)) ≤ 2 * f (x, y)) :
    ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then f (affineRotation (x - 1, y)) + f (affineRotation (x + 1, y))
        else f (affineRotation (x, y - 1)) + f (affineRotation (x, y + 1))) ≤
      2 * f (affineRotation (x, y)) := by
  intro x y
  rw [affineRotation_incoming_sum]
  exact hSuperharmonic (-y) (x - 1)

/-- The actual matrix congruence is the quadratic form of the rotated coordinates. -/
theorem rotation_quadratic (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    LatticeQuadraticRounding.quadratic (rotationMatrix.transpose * M * rotationMatrix) x y =
      LatticeQuadraticRounding.quadratic M (-y) x := by
  norm_num [LatticeQuadraticRounding.quadratic, rotationMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- The original uniform quadratic asymptotic survives the affine rotation,
with the exact congruence matrix and no additional regularity premise. -/
theorem affineRotation_quadratic_growth
    (f : ℤ × ℤ → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |f (x, y) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |f (affineRotation (x, y)) - LatticeQuadraticRounding.quadratic
          (rotationMatrix.transpose * M * rotationMatrix) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  have hShift := QuadraticGrowthTranslation.translate_sub_affine f M 0 (-1) 0 0 0 hGrowth
  intro δ hδ
  obtain ⟨R, hR, hApprox⟩ := hShift δ hδ
  refine ⟨R, hR, ?_⟩
  intro x y hSize
  have hRotSize : R ^ 2 ≤ ((-y : ℤ) : ℝ) ^ 2 + (x : ℝ) ^ 2 := by
    simpa only [Int.cast_neg, neg_sq, add_comm] using hSize
  have h := hApprox (-y) x hRotSize
  rw [rotation_quadratic]
  simpa only [affineRotation, LatticeQuadraticRounding.quadratic, add_zero, zero_mul,
    sub_zero, Int.cast_neg, neg_sq, sub_eq_add_neg, add_comm, neg_zero, zero_add] using h

/-- Adding the same matrix after quarter-turn congruence preserves strict differences. -/
theorem rotated_difference_posDef
    (M N A : Matrix (Fin 2) (Fin 2) ℝ) (hAbove : (M - N).PosDef) :
    (rotationMatrix.transpose * M * rotationMatrix + A -
      (rotationMatrix.transpose * N * rotationMatrix + A)).PosDef := by
  have h := hAbove.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit rotationMatrix_isUnit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, add_sub_add_right_eq_sub] using h

end FLattice.Auxiliary.ElementaryDuality
