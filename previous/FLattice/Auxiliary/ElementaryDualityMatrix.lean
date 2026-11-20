import FLattice.Auxiliary.ElementaryDualityAffine
import FLattice.Auxiliary.BranchMatrix

/-!
# Exact reference-matrix algebra for the elementary duality

The affine quarter-turn and the literal harmonic matrix carry B(n,d) to
B(d-n,d+n). The identity is proved over real parameters, using only the
necessary nonzero denominator. Common nonzero scaling leaves B unchanged.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ElementaryDuality

open BranchMatrix

/-- The transformed denominator is exactly twice the original denominator. -/
theorem dual_denominator (n d : ℝ) :
    denominator (d - n) (d + n) = 2 * denominator n d := by
  unfold denominator
  ring

/-- The exact reference-matrix transformation, with the literal harmonic shift. -/
theorem dual_rankOneMatrix (n d : ℝ) (hDenominator : denominator n d ≠ 0) :
    rotationMatrix.transpose * rankOneMatrix n d * rotationMatrix +
      (!![(1 : ℝ) / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) =
        rankOneMatrix (d - n) (d + n) := by
  rw [rankOneMatrix_entries, rankOneMatrix_entries, dual_denominator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotationMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.add_apply, Fin.sum_univ_two] <;>
    field_simp [hDenominator] <;> unfold denominator <;> ring

/-- Source-range parameters satisfy the dual reference identity, including endpoints. -/
theorem dual_rankOneMatrix_of_source_range (n d : ℝ)
    (hd : 0 < d) (hn : 0 ≤ n) (hnd : n ≤ d) :
    rotationMatrix.transpose * rankOneMatrix n d * rotationMatrix +
      (!![(1 : ℝ) / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) =
        rankOneMatrix (d - n) (d + n) := by
  exact dual_rankOneMatrix n d (ne_of_gt (denominator_pos n d hd hn hnd))

/-- The denominator scales quadratically under a common real scalar. -/
theorem scaled_denominator (n d t : ℝ) :
    denominator (t * n) (t * d) = t ^ 2 * denominator n d := by
  unfold denominator
  ring

/-- A common nonzero real scaling leaves the actual reference matrix unchanged. -/
theorem rankOneMatrix_scale (n d t : ℝ) (ht : t ≠ 0) :
    rankOneMatrix (t * n) (t * d) = rankOneMatrix n d := by
  rw [rankOneMatrix_entries, rankOneMatrix_entries, scaled_denominator]
  by_cases hD : denominator n d = 0
  · simp only [hD, mul_zero, div_zero]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num <;> field_simp [ht, hD]

end FLattice.Auxiliary.ElementaryDuality
