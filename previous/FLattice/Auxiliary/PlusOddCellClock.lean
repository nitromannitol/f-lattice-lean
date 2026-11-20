import FLattice.Auxiliary.PlusOddCellData
import FLattice.Auxiliary.PlusOddBulkClock
import FLattice.Auxiliary.PlusOddPredecessors
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Complete incoming clock selection for the displayed odd table

Every selected index is an actual incoming edge followed by the canonical
cell decoder. This combines all clock overrides and period seams. The
conclusion concerns the displayed deficit table; its equality with the
physical profile deficit is a separate proof obligation.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

private theorem clock_00 {m : Parameter} (c : Cell m) (he : c.e = 0) (hv : c.v = 0) :
    (cellClock (incomingCell c 0) < cellClock c ∨
      cellClock (incomingCell c 1) < cellClock c) ∧
    (cellDeficitTable c = 1 → cellClock (incomingCell c 0) < cellClock c ∧
      cellClock (incomingCell c 1) < cellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨ru, su, eu, vu⟩ := incomingCell_00_up c he hv
  by_cases hTop : c.r = m.val + 1
  · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_top c he hv hTop
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, ru, su, eu, vu,
      rd, sd, ed, vd, hTop]
    omega
  by_cases hEnd : c.r = m.val ∧ c.s = m.val - 1
  · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_penultimate c he hv hEnd.1 hEnd.2
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, ru, su, eu, vu,
      rd, sd, ed, vd, hEnd.1, hEnd.2]
    omega
  · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_inner c he hv (by omega) hEnd
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, ru, su, eu, vu,
      rd, sd, ed, vd]
    omega

private theorem clock_01 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hNotPrescribed : ¬cellPrescribed c) :
    (cellClock (incomingCell c 0) < cellClock c ∨
      cellClock (incomingCell c 1) < cellClock c) ∧
    (cellDeficitTable c = 1 → cellClock (incomingCell c 0) < cellClock c ∧
      cellClock (incomingCell c 1) < cellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hPin : ¬(c.r = m.val + 1 ∧ c.s = m.val - 2) := by
    intro h
    exact hNotPrescribed ⟨h.1, h.2, he, hv⟩
  obtain ⟨rl, sl, el, vl⟩ := incomingCell_01_left c he hv
  by_cases hLast : c.s = m.val - 1
  · obtain ⟨rr, sr, er, vr⟩ := incomingCell_01_right_last c he hv hLast
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rl, sl, el, vl,
      rr, sr, er, vr, hLast]
    omega
  · obtain ⟨rr, sr, er, vr⟩ := incomingCell_01_right_inner c he hv (by omega) hPin
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rl, sl, el, vl,
      rr, sr, er, vr]
    omega

private theorem clock_10 {m : Parameter} (c : Cell m) (he : c.e = 1) (hv : c.v = 0) :
    (cellClock (incomingCell c 0) < cellClock c ∨
      cellClock (incomingCell c 1) < cellClock c) ∧
    (cellDeficitTable c = 1 → cellClock (incomingCell c 0) < cellClock c ∧
      cellClock (incomingCell c 1) < cellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rr, sr, er, vr⟩ := incomingCell_10_right c he hv
  by_cases hs : c.s = 0
  · by_cases hr : c.r = 0
    · obtain ⟨rl, sl, el, vl⟩ := incomingCell_10_left_origin c he hv hr hs
      norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rl, sl, el, vl,
        rr, sr, er, vr, hr, hs]
    · obtain ⟨rl, sl, el, vl⟩ := incomingCell_10_left_of_zero c he hv hs (by omega)
      norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rl, sl, el, vl,
        rr, sr, er, vr, hs]
      omega
  · obtain ⟨rl, sl, el, vl⟩ := incomingCell_10_left_of_pos c he hv (by omega)
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rl, sl, el, vl,
      rr, sr, er, vr]
    omega

private theorem clock_11 {m : Parameter} (c : Cell m) (he : c.e = 1) (hv : c.v = 1) :
    (cellClock (incomingCell c 0) < cellClock c ∨
      cellClock (incomingCell c 1) < cellClock c) ∧
    (cellDeficitTable c = 1 → cellClock (incomingCell c 0) < cellClock c ∧
      cellClock (incomingCell c 1) < cellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_down c he hv
  by_cases hr : c.r = 0
  · by_cases hs : c.s = 0
    · obtain ⟨ru, su, eu, vu⟩ := incomingCell_11_up_origin c he hv hr hs
      norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rd, sd, ed, vd,
        ru, su, eu, vu, hr, hs]
      omega
    · obtain ⟨ru, su, eu, vu⟩ := incomingCell_11_up_row_zero c he hv hr (by omega)
      norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rd, sd, ed, vd,
        ru, su, eu, vu, hr]
      omega
  · obtain ⟨ru, su, eu, vu⟩ := incomingCell_11_up_of_pos c he hv (by omega)
    norm_num [cellClock, cellDeficitTable, bulkClock, he, hv, rd, sd, ed, vd,
      ru, su, eu, vu]
    omega

/-- Off the prescribed cell, at least one actual incoming clock decreases;
when the displayed deficit is one, both actual incoming clocks decrease. -/
theorem cellClock_decreasing_inputs {m : Parameter} (c : Cell m)
    (hNotPrescribed : ¬cellPrescribed c) :
    (cellClock (incomingCell c 0) < cellClock c ∨
      cellClock (incomingCell c 1) < cellClock c) ∧
    (cellDeficitTable c = 1 → cellClock (incomingCell c 0) < cellClock c ∧
      cellClock (incomingCell c 1) < cellClock c) := by
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · exact clock_00 c he hv
  · exact clock_01 c he hv hNotPrescribed
  · exact clock_10 c he hv
  · exact clock_11 c he hv

/-- More actual incoming indices have smaller clocks than the displayed deficit.
The index count retains multiplicity even if two decoded inputs coincide. -/
theorem cell_clock_selected {m : Parameter} (c : Cell m)
    (hNotPrescribed : ¬cellPrescribed c) :
    ∃ S : Finset (Fin 2), cellDeficitTable c < (S.card : ℤ) ∧
      ∀ i ∈ S, cellClock (incomingCell c i) < cellClock c := by
  obtain ⟨hOne, hBoth⟩ := cellClock_decreasing_inputs c hNotPrescribed
  rcases cellDeficitTable_zero_or_one c hNotPrescribed with hZero | hUnit
  · rcases hOne with hLeft | hRight
    · refine ⟨{0}, ?_, ?_⟩
      · simp only [hZero, Finset.card_singleton, Nat.cast_one, zero_lt_one]
      · intro i hi
        have hi0 : i = 0 := Finset.mem_singleton.mp hi
        simpa only [hi0] using hLeft
    · refine ⟨{1}, ?_, ?_⟩
      · simp only [hZero, Finset.card_singleton, Nat.cast_one, zero_lt_one]
      · intro i hi
        have hi1 : i = 1 := Finset.mem_singleton.mp hi
        simpa only [hi1] using hRight
  · obtain ⟨hLeft, hRight⟩ := hBoth hUnit
    refine ⟨Finset.univ, ?_, ?_⟩
    · norm_num [hUnit]
    · intro i _
      fin_cases i
      · exact hLeft
      · exact hRight

end FLattice.Auxiliary.PlusOddProfile
