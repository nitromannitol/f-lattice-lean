import FLattice.Auxiliary.PlusEvenLowDeficit
import FLattice.Auxiliary.PlusEvenBulkDeficit
import FLattice.Auxiliary.PlusEvenSeamDeficit

/-!
# Complete physical deficit table on the even-plus representatives

The four identities exhaust the representative domain. They combine actual
physical incoming-star calculations, including all low rows and period seams.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- Complete `00` deficit formula on every valid representative. -/
theorem incomingDeficit_00_at_cell (m : Parameter) (r s : ℤ)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s) 0 =
      if r = 0 then 0 else if r = 1 then (if s = 0 then 1 else 0)
      else if r - s = 2 then 1 else 0 := by
  by_cases h0 : r = 0
  · subst r
    simpa using incomingDeficit_00_row_zero m s hs0 hsm
  by_cases h1 : r = 1
  · subst r
    simpa using incomingDeficit_00_row_one m s hs0 hsm
  rw [if_neg h0, if_neg h1]
  by_cases hs : s = 0
  · subst s
    simpa using incomingDeficit_00_left m r (by omega) hrm
  · exact incomingDeficit_00_bulk m r s (by omega) hrm (by omega) hsm hMissing

/-- Complete `01` deficit formula, including both downward wraps. -/
theorem incomingDeficit_01_at_cell (m : Parameter) (r s : ℤ)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s + 1) 0 =
      if r ≤ 1 then (if 1 ≤ s then 1 else 0)
      else if r - s = 1 ∨ r - s = 3 then 0 else 1 := by
  by_cases h0 : r = 0
  · subst r
    simpa using incomingDeficit_01_row_zero m s hs0 hsm
  by_cases h1 : r = 1
  · subst r
    simpa using incomingDeficit_01_row_one m s hs0 hsm
  rw [if_neg (by omega : ¬r ≤ 1)]
  by_cases hTop : r = m.val + 1
  · subst r
    rw [incomingDeficit_01_top m s hs0 (by omega)]
    split_ifs <;> omega
  by_cases hNext : r = m.val ∧ s = m.val - 1
  · obtain ⟨rfl, rfl⟩ := hNext
    rw [incomingDeficit_01_penultimate_right]
    split_ifs <;> omega
  · exact incomingDeficit_01_bulk m r s (by omega) (by omega) hs0 hsm hNext

/-- Complete `10` deficit formula, retaining the value four on the prescribed class. -/
theorem incomingDeficit_10_at_cell (m : Parameter) (r s : ℤ)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s) 1 =
      if r = 0 then (if s = 0 then 4 else 0)
      else if r = 1 then (if 1 ≤ s then 1 else 0)
      else if r - s = 1 ∨ r - s = 3 then 0 else 1 := by
  by_cases h0 : r = 0
  · subst r
    simpa using incomingDeficit_10_row_zero m s hs0 hsm
  by_cases h1 : r = 1
  · subst r
    simpa using incomingDeficit_10_row_one m s hs0 hsm
  rw [if_neg h0, if_neg h1]
  exact incomingDeficit_10_bulk m r s (by omega) hrm hs0 hsm hMissing

/-- Complete `11` deficit formula with both last-column alterations. -/
theorem incomingDeficit_11_at_cell (m : Parameter) (r s : ℤ)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    incomingDeficit m (2 * m.val * r + 2 * s + 1) 1 =
      if r ≤ 1 then 0 else if s = m.val - 1 then 1
      else if r = m.val + 1 ∧ s = m.val - 2 then 0
      else if r - s = 3 then 1 else 0 := by
  by_cases h0 : r = 0
  · subst r
    simpa using incomingDeficit_11_row_zero m s hs0 hsm
  by_cases h1 : r = 1
  · subst r
    simpa using incomingDeficit_11_row_one m s hs0 hsm
  rw [if_neg (by omega : ¬r ≤ 1)]
  by_cases hLast : s = m.val - 1
  · subst s
    rw [if_pos rfl]
    exact incomingDeficit_11_right m r (by omega) (by omega)
  rw [if_neg hLast]
  by_cases hTop : r = m.val + 1 ∧ s = m.val - 2
  · obtain ⟨rfl, rfl⟩ := hTop
    rw [if_pos ⟨rfl, rfl⟩]
    exact incomingDeficit_11_top_endpoint m
  rw [if_neg hTop]
  exact incomingDeficit_11_bulk m r s (by omega) hrm hs0 (by omega) hTop

end FLattice.Auxiliary.PlusEvenProfile
