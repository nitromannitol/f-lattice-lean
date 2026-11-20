import FLattice.Auxiliary.PlusOddCoordinates
import FLattice.Auxiliary.PlusOddPeriods

/-!
# Exact prescribed and added-orbit values of the odd-plus profile

Every assertion concerns the literal corrected global profile. Signed
coordinate lifts establish the full prescribed coset and the six values
used at the two added orbits. No star, rank, comparison or escape property
is asserted here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile PlusOddBulk

private theorem height_top_00 (m : Parameter) :
    representativeHeight m 0 0 (m.val + 1) (m.val - 2) =
      -m.val ^ 2 - m.val + 2 := by
  have hm := m.property
  have hrow : ¬(m.val + 1 = 0 ∨ m.val + 1 = 1) := by omega
  have hlast : m.val - 2 ≠ m.val - 1 := by omega
  unfold representativeHeight
  rw [if_neg hrow]
  norm_num [hlast, v00,
    show m.val + 1 - (m.val - 2) = 3 by omega]
  ring

private theorem height_top_01 (m : Parameter) :
    representativeHeight m 0 1 (m.val + 1) (m.val - 2) =
      -m.val ^ 2 - m.val + 2 := by
  have hm := m.property
  have hrow : ¬(m.val + 1 = 0 ∨ m.val + 1 = 1) := by omega
  have hlast : m.val - 2 ≠ m.val - 1 := by omega
  unfold representativeHeight
  rw [if_neg hrow]
  norm_num [hlast, v01,
    show m.val + 1 - (m.val - 2) = 3 by omega]
  ring

private theorem height_top_10 (m : Parameter) :
    representativeHeight m 1 0 (m.val + 1) (m.val - 2) =
      -m.val ^ 2 + 2 := by
  have hm := m.property
  have hrow : ¬(m.val + 1 = 0 ∨ m.val + 1 = 1) := by omega
  have hlast : m.val - 2 ≠ m.val - 1 := by omega
  unfold representativeHeight
  rw [if_neg hrow]
  norm_num [hlast, v10,
    show m.val + 1 - (m.val - 2) = 3 by omega]
  ring

private theorem profile_low_row_zero (m : Parameter) (s : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s < m.val) :
    profile m (2 * s + (v.val : ℤ)) (e.val : ℤ) = 0 := by
  have hm := m.property
  have h := profile_at_lifted_cell m 0 s 0 0 e v
    (by omega) (by omega) hs hsm (by omega)
  simpa [representativeHeight] using h

/-- The literal global profile is zero at the origin. -/
theorem profile_origin (m : Parameter) : profile m 0 0 = 0 := by
  have hm := m.property
  simpa using profile_low_row_zero m 0 0 0 (by omega) (by omega)

/-- Every signed point of the prescribed coset has its exact quadratic value. -/
theorem profile_prescribed_coset (m : Parameter) (a b : ℤ) :
    profile m
      (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b)
      (-2 * m.val * a - 2 * b) =
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) := by
  have hm := m.property
  have h := profile_at_lifted_cell m (m.val + 1) (m.val - 2)
    (-m.val * a - b) (-a - 1) 0 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_top_01] at h
  norm_num at h
  unfold halfPeriod at h ⊢
  ring_nf at h ⊢
  exact h

/-- The prescribed point is `D = (-1, 0)` and has height one. -/
theorem profile_prescribed_point (m : Parameter) : profile m (-1) 0 = 1 := by
  simpa using profile_prescribed_coset m 0 0

/-- The first additional orbit begins at `P₀ = (-2, 0)`, of height zero. -/
theorem profile_added_point (m : Parameter) : profile m (-2) 0 = 0 := by
  have hm := m.property
  have h := profile_at_lifted_cell m (m.val + 1) (m.val - 2) 0 (-1) 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_top_00] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h
  exact h

/-- The upward neighbor of `P₀` also has height zero. -/
theorem profile_added_point_up (m : Parameter) : profile m (-2) 1 = 0 := by
  have hm := m.property
  have h := profile_at_lifted_cell m (m.val + 1) (m.val - 2) 0 (-1) 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_top_10] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h
  exact h

/-- The second additional orbit begins at `A₀ = (2m-2, 1)`, of height zero. -/
theorem profile_added_neighbor (m : Parameter) :
    profile m (2 * m.val - 2) 1 = 0 := by
  have hm := m.property
  have h := profile_low_row_zero m (m.val - 1) 1 0 (by omega) (by omega)
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The left input of `A₀` has height zero. -/
theorem profile_added_neighbor_left (m : Parameter) :
    profile m (2 * m.val - 3) 1 = 0 := by
  have hm := m.property
  have h := profile_low_row_zero m (m.val - 2) 1 1 (by omega) (by omega)
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The point `B₀ = (2m-1, 1)` has height zero. -/
theorem profile_added_successor (m : Parameter) :
    profile m (2 * m.val - 1) 1 = 0 := by
  have hm := m.property
  have h := profile_low_row_zero m (m.val - 1) 1 1 (by omega) (by omega)
  norm_num at h
  ring_nf at h ⊢
  exact h

/-- The downward neighbor of `P₀` is `A₀-(2m,2)` and has height zero. -/
theorem profile_added_point_down (m : Parameter) : profile m (-2) (-1) = 0 := by
  have h := profile_add_diagonal_period m (-2) (-1)
  rw [show -2 + 2 * m.val = 2 * m.val - 2 by ring] at h
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.reduceSub] at h
  rw [profile_added_neighbor] at h
  omega

end FLattice.Auxiliary.PlusOddProfile
