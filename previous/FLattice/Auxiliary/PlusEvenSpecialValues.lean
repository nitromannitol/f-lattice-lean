import FLattice.Auxiliary.PlusEvenCoordinates
import FLattice.Auxiliary.PlusEvenRepresentative

/-!
# Exact physical values of the even-plus profile

Every identity below is obtained from the proved lifted-cell formula and
corrected representative evaluations. In particular, the prescribed-coset
theorem covers all signed integer indices without finite sampling.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The even-plus profile has value `-1` at the origin. -/
theorem profile_origin (m : Parameter) : profile m 0 0 = -1 := by
  have hm := m.property
  have h := profile_at_lifted_cell m 0 0 0 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_00_row_zero 0 (by omega)] at h
  norm_num at h
  exact h

/-- The corrected prescribed representative has value zero. -/
theorem profile_prescribed_representative (m : Parameter) : profile m 0 1 = 0 := by
  have hm := m.property
  have h := profile_at_lifted_cell m 0 0 0 0 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_10_row_zero 0 (by omega)] at h
  norm_num at h
  exact h

/-- The wrapped site immediately left of the origin has value `-1`. -/
theorem profile_left_of_origin (m : Parameter) : profile m (-1) 0 = -1 := by
  have hm := m.property
  have h := profile_at_lifted_cell m (m.val + 1) (m.val - 2) 0 (-1) 0 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_01_upper_left] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h
  exact h

/-- The first even-column value two rows above the origin. -/
theorem profile_above_origin (m : Parameter) : profile m 0 2 = -3 := by
  have hm := m.property
  have h := profile_at_lifted_cell m m.val (m.val - 1) 1 (-1) 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_00_upper_left] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h
  exact h

/-- The entire even-column segment at height two has the same value. -/
theorem profile_even_segment (m : Parameter) (s : ℤ) (hs0 : 0 ≤ s)
    (hsm : s < m.val) : profile m (2 * s) 2 = -3 := by
  by_cases hs : s = 0
  · subst s
    simpa only [mul_zero] using profile_above_origin m
  · have hm := m.property
    have h := profile_at_lifted_cell m (m.val + 1) (s - 1) 1 (-1) 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [height_00_upper_row m.val s (by omega)] at h
    norm_num at h
    unfold halfPeriod at h
    ring_nf at h ⊢
    exact h

/-- Every signed index of the prescribed coset has exactly the prescribed height. -/
theorem profile_prescribed_coset (m : Parameter) (a b : ℤ) :
    profile m (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b)
      (-1 - 2 * m.val * a - 2 * b) =
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) := by
  have hm := m.property
  have h := profile_at_lifted_cell m 0 0 (-1 - m.val * a - b) (-a) 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_10_row_zero 0 (by omega)] at h
  norm_num at h
  unfold halfPeriod at h ⊢
  ring_nf at h ⊢
  exact h

/-- The distinguished point `D=(-2m,-1)` has height one. -/
theorem profile_prescribed_point (m : Parameter) : profile m (-2 * m.val) (-1) = 1 := by
  simpa using profile_prescribed_coset m 0 0

end FLattice.Auxiliary.PlusEvenProfile
