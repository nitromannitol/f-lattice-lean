import FLattice.Auxiliary.PlusEvenPhysicalCells
import FLattice.Auxiliary.PlusEvenSpecialValues

/-!
# The five physical seam families of the even-plus profile

These are exact incoming deficits of the literal global profile. Every
wrapped input is identified by a valid cell, an affine period, or a signed
lifted cell before its representative value is used. The module does not
assert that these families cover all sites or prove a global comparison.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The left seam of state `00`, including its first row above the low rows. -/
theorem incomingDeficit_00_left (m : Parameter) (r : ℤ)
    (hr : 2 ≤ r) (hrm : r ≤ m.val + 1) :
    incomingDeficit m (2 * m.val * r) 0 = if r = 2 then 1 else 0 := by
  have hm := m.property
  have hCenter := profile_at_cell m r 0 0 0
    (by omega) hrm (by omega) (by omega) (by omega)
  have hLeft := profile_at_cell m (r - 1) (m.val - 1) 0 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hRight := profile_at_cell m r 0 0 1
    (by omega) hrm (by omega) (by omega) (by omega)
  rw [height_01_wrapped_left m.val r hrm] at hLeft
  have hStar := incomingDeficit_00 m r 0
  norm_num at hCenter hLeft hRight hStar
  by_cases hTwo : r = 2
  · subst r
    rw [height_00_left_two] at hCenter
    have hValue : representativeHeight 0 1 2 0 = -3 := by decide
    rw [hValue] at hRight
    norm_num at hCenter hLeft hRight ⊢
    ring_nf at hCenter hLeft hRight hStar ⊢
    omega
  · rw [height_00_left r (by omega)] at hCenter
    rw [height_01_left r (by omega)] at hRight
    rw [if_neg hTwo]
    ring_nf at hCenter hLeft hRight hStar ⊢
    omega

/-- The last-column seam of state `11` before the top endpoint. -/
theorem incomingDeficit_11_right (m : Parameter) (r : ℤ)
    (hr : 2 ≤ r) (hrm : r ≤ m.val) :
    incomingDeficit m (2 * m.val * r + 2 * (m.val - 1) + 1) 1 = 1 := by
  have hm := m.property
  have hCenter := profile_at_cell m r (m.val - 1) 1 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hLeft := profile_at_cell m r (m.val - 1) 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hRight := profile_at_cell m (r + 1) 0 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_11_right m.val r hr hrm] at hCenter
  rw [height_10_right m.val r hr hrm] at hLeft
  rw [height_10_wrapped_right r hr] at hRight
  have hStar := incomingDeficit_11 m r (m.val - 1)
  norm_num at hCenter hLeft hRight
  ring_nf at hCenter hLeft hRight hStar ⊢
  omega

/-- The altered `11` deficit at the truncated top endpoint is zero. -/
theorem incomingDeficit_11_top_endpoint (m : Parameter) :
    incomingDeficit m (2 * m.val * (m.val + 1) + 2 * (m.val - 2) + 1) 1 = 0 := by
  have hm := m.property
  have hCenter := profile_at_cell m (m.val + 1) (m.val - 2) 1 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hLeft := profile_at_cell m (m.val + 1) (m.val - 2) 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_11_upper_left] at hCenter
  rw [height_10_upper_left] at hLeft
  have hRight := profile_add_horizontal_period m 0 1
  rw [profile_prescribed_representative] at hRight
  have hStar := incomingDeficit_11 m (m.val + 1) (m.val - 2)
  norm_num at hCenter hLeft hRight
  unfold halfPeriod at hRight
  ring_nf at hCenter hLeft hRight hStar ⊢
  omega

/-- The downward input at a top-row `01` center uses a signed lifted cell. -/
private theorem profile_01_top_down (m : Parameter) (s : ℤ)
    (hs0 : 0 ≤ s) (hsm : s ≤ m.val - 2) :
    profile m (2 * m.val * (m.val + 1) + 2 * s + 1) (-1) =
      -(m.val ^ 2) - m.val - 2 * s - 3 := by
  have hm := m.property
  have h := profile_at_lifted_cell m 0 (s + 1) (-1) 1 1 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_11_row_zero (s + 1) (by omega), if_neg (by omega)] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

/-- The full top-row seam of state `01`, including its final representative. -/
theorem incomingDeficit_01_top (m : Parameter) (s : ℤ)
    (hs0 : 0 ≤ s) (hsm : s ≤ m.val - 2) :
    incomingDeficit m (2 * m.val * (m.val + 1) + 2 * s + 1) 0 =
      if s = m.val - 2 then 0 else 1 := by
  have hm := m.property
  have hCenter := profile_at_cell m (m.val + 1) s 0 1
    (by omega) (by omega) hs0 (by omega) (by omega)
  have hUp := profile_at_cell m (m.val + 1) s 1 1
    (by omega) (by omega) hs0 (by omega) (by omega)
  rw [height_01_top m.val s hsm] at hCenter
  have hDown := profile_01_top_down m s hs0 hsm
  have hStar := incomingDeficit_01 m (m.val + 1) s
  norm_num at hCenter hUp
  by_cases hLast : s = m.val - 2
  · subst s
    rw [height_11_upper_left] at hUp
    rw [if_pos rfl]
    ring_nf at hCenter hDown hUp hStar ⊢
    omega
  · rw [height_11_top m.val s (by omega)] at hUp
    rw [if_neg hLast]
    ring_nf at hCenter hDown hUp hStar ⊢
    omega

/-- The downward input at the penultimate-row `01` endpoint uses the
exceptional `11(0,0)` representative. -/
private theorem profile_01_penultimate_down (m : Parameter) :
    profile m (2 * m.val * m.val + 2 * (m.val - 1) + 1) (-1) =
      -(m.val ^ 2) - m.val := by
  have hm := m.property
  have h := profile_at_lifted_cell m 0 0 (-1) 1 1 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_11_row_zero 0 (by omega)] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

/-- The final `01` cell of row `m` has zero physical incoming deficit. -/
theorem incomingDeficit_01_penultimate_right (m : Parameter) :
    incomingDeficit m (2 * m.val * m.val + 2 * (m.val - 1) + 1) 0 = 0 := by
  have hm := m.property
  have hCenter := profile_at_cell m m.val (m.val - 1) 0 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hUp := profile_at_cell m m.val (m.val - 1) 1 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_01_penultimate_right] at hCenter
  rw [height_11_right m.val m.val hm (by omega)] at hUp
  have hDown := profile_01_penultimate_down m
  have hStar := incomingDeficit_01 m m.val (m.val - 1)
  norm_num at hCenter hUp
  ring_nf at hCenter hDown hUp hStar ⊢
  omega

end FLattice.Auxiliary.PlusEvenProfile
