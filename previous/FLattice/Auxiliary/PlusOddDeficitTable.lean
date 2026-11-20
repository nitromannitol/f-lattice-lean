import FLattice.Auxiliary.PlusOddIncomingValues
import FLattice.Auxiliary.PlusOddIncomingSums
import FLattice.Auxiliary.PlusOddPhysicalCells
import FLattice.Auxiliary.PlusOddCellData

/-!
# The displayed odd-plus deficit table is the actual physical deficit

Every incoming height is first evaluated at the literal physical star.
The remaining calculation includes both corrected low rows, the last
column, and all period seams. No displayed deficit is assumed to equal
the physical one.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile PlusOddBulk

private theorem deficit_at_cell_inputs {m : Parameter} (c : Cell m) :
    incomingDeficit m c.x c.y = 2 * representativeHeight m c.e c.v c.r c.s -
      profile m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 -
      profile m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 := by
  have h := profile_at_cell m c.r c.s c.e c.v c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  change profile m c.x c.y = _ at h
  rw [incomingDeficit_eq_residual, Fin.sum_univ_two, h]
  ring

private theorem deficit_00 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) :
    incomingDeficit m c.x c.y = cellDeficitTable c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rw [deficit_at_cell_inputs, profile_incoming_00_up c he hv]
  by_cases hTop : c.r = m.val + 1
  · rw [profile_incoming_00_down_top c he hv hTop]
    norm_num [cellDeficitTable, representativeHeight, he, hv, hTop, v00, v10]
    split_ifs <;> ring_nf <;> omega
  · by_cases hEnd : c.r = m.val ∧ c.s = m.val - 1
    · rw [profile_incoming_00_down_penultimate c he hv hEnd.1 hEnd.2]
      norm_num [cellDeficitTable, representativeHeight, he, hv, hEnd.1, hEnd.2, v00, v10]
      split_ifs <;> ring_nf <;> omega
    · rw [profile_incoming_00_down_inner c he hv (by omega) hEnd]
      by_cases hrZero : c.r = 0
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, v00, v10]
      · by_cases hrOne : c.r = 1
        · norm_num [cellDeficitTable, representativeHeight, he, hv, hrOne, v00, v10]
          split_ifs <;> omega
        · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hrOne, v00, v10]
          split_ifs <;> ring_nf <;> omega

private theorem deficit_01 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) :
    incomingDeficit m c.x c.y = cellDeficitTable c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rw [deficit_at_cell_inputs, profile_incoming_01_left c he hv]
  by_cases hLast : c.s = m.val - 1
  · rw [profile_incoming_01_right_last c he hv hLast]
    by_cases hrZero : c.r = 0
    · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hLast, v00, v01]
    · by_cases hrOne : c.r = 1
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrOne, hLast, v00, v01]
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hrOne, hLast, v00, v01]
        split_ifs <;> ring_nf <;> omega
  · by_cases hEnd : c.r = m.val + 1 ∧ c.s = m.val - 2
    · rw [profile_incoming_01_right_top_endpoint c he hv hEnd.1 hEnd.2]
      norm_num [cellDeficitTable, representativeHeight, he, hv, hEnd.1, hEnd.2,
        v00, v01, halfPeriod]
      split_ifs <;> ring_nf <;> omega
    · rw [profile_incoming_01_right_inner c he hv (by omega) hEnd]
      by_cases hrZero : c.r = 0
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, v00, v01]
      · by_cases hrOne : c.r = 1
        · norm_num [cellDeficitTable, representativeHeight, he, hv, hrOne, hLast, v00, v01]
        · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hrOne, hLast,
            hEnd, v00, v01]
          split_ifs <;> ring_nf <;> omega

private theorem deficit_10 {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) :
    incomingDeficit m c.x c.y = cellDeficitTable c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rw [deficit_at_cell_inputs, profile_incoming_10_right c he hv]
  by_cases hsZero : c.s = 0
  · by_cases hrZero : c.r = 0
    · rw [profile_incoming_10_left_origin c he hv hrZero hsZero]
      norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hsZero, v10, v11]
      split_ifs <;> ring_nf
      omega
    · rw [profile_incoming_10_left_of_zero c he hv hsZero (by omega)]
      by_cases hrOne : c.r = 1
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrOne, hsZero, v10, v11]
      · by_cases hrTwo : c.r = 2
        · norm_num [cellDeficitTable, representativeHeight, he, hv, hrTwo, hsZero, v10, v11]
          omega
        · have hPrev : ¬(c.r - 1 = 0 ∨ c.r - 1 = 1) := by omega
          norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hrOne,
            hPrev, hsZero, v10, v11]
          split_ifs <;> ring_nf <;> omega
  · rw [profile_incoming_10_left_of_pos c he hv (by omega)]
    by_cases hrZero : c.r = 0
    · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, v10, v11]
    · by_cases hrOne : c.r = 1
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrOne, v10, v11]
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hrOne, v10, v11]
        split_ifs <;> ring_nf <;> omega

private theorem deficit_11 {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) :
    incomingDeficit m c.x c.y = cellDeficitTable c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rw [deficit_at_cell_inputs, profile_incoming_11_down c he hv]
  by_cases hrZero : c.r = 0
  · by_cases hsZero : c.s = 0
    · rw [profile_incoming_11_up_origin c he hv hrZero hsZero]
      norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hsZero, v01, v11]
      split_ifs <;> ring_nf <;> omega
    · rw [profile_incoming_11_up_row_zero c he hv hrZero (by omega)]
      norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, v01, v11]
      split_ifs <;> ring_nf <;> omega
  · rw [profile_incoming_11_up_of_pos c he hv (by omega)]
    by_cases hrOne : c.r = 1
    · norm_num [cellDeficitTable, representativeHeight, he, hv, hrOne, v01, v11]
    · by_cases hrTwo : c.r = 2
      · norm_num [cellDeficitTable, representativeHeight, he, hv, hrTwo, v01, v11]
        split_ifs <;> ring_nf <;> omega
      · have hPrev : ¬(c.r - 1 = 0 ∨ c.r - 1 = 1) := by omega
        norm_num [cellDeficitTable, representativeHeight, he, hv, hrZero, hrOne,
          hPrev, v01, v11]
        split_ifs <;> ring_nf <;> omega

/-- The complete displayed table equals the literal physical incoming deficit
at every valid representative, including all low rows and period seams. -/
theorem incomingDeficit_at_cell {m : Parameter} (c : Cell m) :
    incomingDeficit m c.x c.y = cellDeficitTable c := by
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he
  · rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
    · exact deficit_00 c he hv
    · exact deficit_01 c he hv
  · rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
    · exact deficit_10 c he hv
    · exact deficit_11 c he hv

end FLattice.Auxiliary.PlusOddProfile
