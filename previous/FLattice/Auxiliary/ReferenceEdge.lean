import FLattice.Auxiliary.BranchMatrix
import FLattice.Auxiliary.MatrixCoordinates

/-!
# The first-quadrant edge is exactly the reference curve

An explicit inverse parameter covers both endpoints and every intermediate
real edge point. Only nonnegative coordinates with sum one are assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ReferenceEdge

open BranchMatrix MatrixCoordinates

/-- Every first-quadrant unit-diamond edge point has an actual reference slope. -/
theorem exists_reference (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : u + v = 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      rankOneMatrix r 1 = matrix u v (-radius u v) := by
  let R := radius u v
  have hR0 : 0 ≤ R := radius_nonneg u v
  have hR2 : R ^ 2 = u ^ 2 + v ^ 2 := radius_sq u v
  have hRpos : 0 < R := by
    by_contra h
    have hz : R = 0 := le_antisymm (le_of_not_gt h) hR0
    have hu0 : u = 0 := by nlinarith only [hR2, hz, sq_nonneg v]
    have hv0 : v = 0 := by nlinarith only [hR2, hz, sq_nonneg u]
    linarith only [hsum, hu0, hv0]
  have ht : 0 < R + u := add_pos_of_pos_of_nonneg hRpos hu
  have hvR : v ≤ R := by nlinarith only [hR2, hR0, hv, sq_nonneg u]
  let r := v / (R + u)
  have hr0 : 0 ≤ r := div_nonneg hv (le_of_lt ht)
  have hr1 : r ≤ 1 := (div_le_one ht).mpr (by linarith only [hvR, hu])
  refine ⟨r, hr0, hr1, ?_⟩
  have hsum' : (u + v) * (R + u) = R + u := by rw [hsum, one_mul]
  have hDen : denominator r 1 = 2 / (R + u) := by
    dsimp [r, denominator]
    field_simp
    nlinarith only [hR2, hsum']
  rw [rankOneMatrix_entries, hDen]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [matrix, mul_one, one_pow]
  · dsimp [r]
    field_simp
    nlinarith only [hR2]
  · dsimp [r]
    field_simp
  · dsimp [r]
    field_simp
  · field_simp
    dsimp [R]
    ring

end FLattice.Auxiliary.ReferenceEdge
