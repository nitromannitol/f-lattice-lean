import FLattice.Auxiliary.PlusEvenPhysicalCells
import FLattice.Auxiliary.PlusEvenRepresentative

/-!
# Physical deficit formulas away from the even-plus seams

Each statement evaluates the literal global incoming deficit. The hypotheses
ensure that the displayed predecessor representatives are valid; the vertical
height corrections are obtained from the proved affine extension.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

open PlusEvenBulk

/-- The `00` physical star is unwrapped when `s` is positive. -/
theorem incomingDeficit_00_bulk (m : Parameter) (r s : ℤ)
    (hr : 2 ≤ r) (hrm : r ≤ m.val + 1)
    (hs : 1 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s) 0 =
      if r - s = 2 then 1 else 0 := by
  have hCenter := profile_at_cell m r s 0 0 (by omega) hrm (by omega) hsm hMissing
  have hLeft := profile_at_cell m r (s - 1) 0 1
    (by omega) hrm (by omega) (by omega) (by omega)
  have hRight := profile_at_cell m r s 0 1 (by omega) hrm (by omega) hsm hMissing
  norm_num at hCenter hLeft hRight
  rw [height_00_eq] at hCenter
  rw [height_01_eq] at hLeft hRight
  have hLeft' : profile m (2 * m.val * r + 2 * s - 1) 0 = u01 r (s - 1) := by
    convert hLeft using 2
    ring
  rw [incomingDeficit_00, hCenter, hLeft', hRight]
  exact u00_deficit r s

/-- The `01` physical star is unwrapped unless its downward cell leaves the domain. -/
theorem incomingDeficit_01_bulk (m : Parameter) (r s : ℤ)
    (hr : 2 ≤ r) (hrm : r ≤ m.val)
    (hs : 0 ≤ s) (hsm : s < m.val)
    (hNext : ¬(r = m.val ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s + 1) 0 =
      if r - s = 1 ∨ r - s = 3 then 0 else 1 := by
  have hCenter := profile_at_cell m r s 0 1
    (by omega) (by omega) hs hsm (by omega)
  have hUp := profile_at_cell m r s 1 1
    (by omega) (by omega) hs hsm (by omega)
  have hDown := profile_at_lifted_cell m (r + 1) s (-1) 0 1 1
    (by omega) (by omega) hs hsm (by omega)
  norm_num at hCenter hUp hDown
  rw [height_01_eq] at hCenter
  rw [height_11_eq, if_neg (by omega)] at hUp hDown
  have hDown' : profile m (2 * m.val * r + 2 * s + 1) (-1) =
      u11 (r + 1) s + 1 := by
    convert hDown using 2
    ring
  rw [incomingDeficit_01, hCenter, hDown', hUp]
  exact u01_deficit r s

/-- Both predecessors of a `10` center above the low rows have valid representatives. -/
theorem incomingDeficit_10_bulk (m : Parameter) (r s : ℤ)
    (hr : 2 ≤ r) (hrm : r ≤ m.val + 1)
    (hs : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s) 1 =
      if r - s = 1 ∨ r - s = 3 then 0 else 1 := by
  have hCenter := profile_at_cell m r s 1 0 (by omega) hrm hs hsm hMissing
  have hDown := profile_at_cell m r s 0 0 (by omega) hrm hs hsm hMissing
  have hUp := profile_at_lifted_cell m (r - 1) s 1 0 0 0
    (by omega) (by omega) hs hsm (by omega)
  norm_num at hCenter hDown hUp
  rw [height_10_eq, if_neg (by omega)] at hCenter
  rw [height_00_eq] at hDown hUp
  have hUp' : profile m (2 * m.val * r + 2 * s) 2 = u00 (r - 1) s - 2 := by
    rw [show 2 * m.val * r + 2 * s =
      2 * m.val * (r - 1) + 2 * s + 2 * m.val by ring, hUp]
    ring
  rw [incomingDeficit_10, hCenter, hDown, hUp']
  exact u10_deficit r s

/-- The `11` physical star is unwrapped before its row's right endpoint. -/
theorem incomingDeficit_11_bulk (m : Parameter) (r s : ℤ)
    (hr : 2 ≤ r) (hrm : r ≤ m.val + 1)
    (hs : 0 ≤ s) (hsm : s ≤ m.val - 2)
    (hNext : ¬(r = m.val + 1 ∧ s = m.val - 2)) :
    incomingDeficit m (2 * m.val * r + 2 * s + 1) 1 =
      if r - s = 3 then 1 else 0 := by
  have hCenter := profile_at_cell m r s 1 1
    (by omega) hrm hs (by omega) (by omega)
  have hLeft := profile_at_cell m r s 1 0
    (by omega) hrm hs (by omega) (by omega)
  have hRight := profile_at_cell m r (s + 1) 1 0
    (by omega) hrm (by omega) (by omega) (by omega)
  norm_num at hCenter hLeft hRight
  rw [height_11_eq, if_neg (by omega)] at hCenter
  rw [height_10_eq, if_neg (by omega)] at hLeft hRight
  have hRight' : profile m (2 * m.val * r + 2 * s + 2) 1 = u10 r (s + 1) := by
    convert hRight using 2
    ring
  rw [incomingDeficit_11, hCenter, hLeft, hRight']
  exact u11_deficit r s

end FLattice.Auxiliary.PlusEvenProfile
