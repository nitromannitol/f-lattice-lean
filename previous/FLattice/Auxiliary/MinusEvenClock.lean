import FLattice.Auxiliary.MinusEvenDeficit
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# A bounded clock for the two even-minus paths

The source's left and right four-phase paths occupy separate clock bands.
The seven-state junction has clocks at most four; its prescribed exit has
clock zero. The remaining branching cells have the largest clock. Every
clock inequality below concerns actual physical incoming edges decoded by
`incomingCell`, including all period seams. No recurrence claim is made.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The representative of the even-minus prescribed coset. -/
def evenCellPrescribed {m : Parameter} (c : Cell m) : Prop :=
  c.r = 1 ∧ c.s = 1 ∧ c.e = 1 ∧ c.v = 0

/-- A bounded integer clock realizing the two source paths and their junction.
The left phases have offsets 0,3,2,1 in order 00,01,11,10. The right
phases have offsets 2,1,0,3. Row-zero right paths use column s-1. -/
def evenCellClock {m : Parameter} (c : Cell m) : ℤ :=
  if c.e = 0 then
    if c.v = 0 then
      if c.r ≤ 1 then (if c.s = 0 then 3 else 8 + 4 * c.s)
      else if c.r - c.s ≤ 0 then 8 + 4 * c.s
      else if c.r - c.s = 1 then 8 * m.val + 20 else 8 * m.val - 4 * c.s + 2
    else
      if c.r ≤ 1 then (if c.s = 0 then 2 else 11 + 4 * c.s)
      else if c.r - c.s ≤ 1 then 11 + 4 * c.s else 8 * m.val - 4 * c.s + 1
  else if c.v = 0 then
    if c.r = 0 then (if c.s = 0 then 4 else 8 * m.val - 4 * c.s + 7)
    else if c.r = 1 then (if c.s = 0 then 4 else if c.s = 1 then 0 else 9 + 4 * c.s)
    else if c.r - c.s ≤ 1 then 9 + 4 * c.s else 8 * m.val - 4 * c.s + 3
  else
    if c.r = 0 then (if c.s = 0 then 8 * m.val + 20 else 8 * m.val - 4 * c.s + 4)
    else if c.r = 1 then (if c.s = 0 then 1 else 10 + 4 * c.s)
    else if c.r - c.s ≤ 1 then 10 + 4 * c.s
    else if c.r - c.s = 2 then 8 * m.val + 20 else 8 * m.val - 4 * c.s

/-- The clock is bounded below on the complete valid cell domain. -/
theorem evenCellClock_nonneg {m : Parameter} (c : Cell m) : 0 ≤ evenCellClock c := by
  have hm := m.property
  have hs0 := c.hs0
  have hsm := c.hsm
  unfold evenCellClock
  split_ifs <;> omega

/-- The same explicit interval bounds every clock, uniformly over valid cells. -/
theorem evenCellClock_le {m : Parameter} (c : Cell m) :
    evenCellClock c ≤ 8 * m.val + 20 := by
  have hm := m.property
  have hs0 := c.hs0
  have hsm := c.hsm
  unfold evenCellClock
  split_ifs <;> omega

private theorem clock_00 {m : Parameter} (c : Cell m) (he : c.e = 0) (hv : c.v = 0) :
    (evenCellClock (incomingCell c 0) < evenCellClock c ∨
      evenCellClock (incomingCell c 1) < evenCellClock c) ∧
    (evenCellDeficit c = 1 → evenCellClock (incomingCell c 0) < evenCellClock c ∧
      evenCellClock (incomingCell c 1) < evenCellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rr, sr, er, vr⟩ := incomingCell_00_right c he hv
  by_cases hs : c.s = 0
  · by_cases hr : c.r = 0
    · obtain ⟨rl, sl, el, vl⟩ := incomingCell_00_left_origin c he hv hr hs
      norm_num [evenCellClock, evenCellDeficit, he, hv, rr, sr, er, vr, rl, sl, el, vl, hr, hs]
    · obtain ⟨rl, sl, el, vl⟩ := incomingCell_00_left_of_zero c he hv hs (by omega)
      norm_num [evenCellClock, evenCellDeficit, he, hv, rr, sr, er, vr, rl, sl, el, vl, hs]
      omega
  · obtain ⟨rl, sl, el, vl⟩ := incomingCell_00_left_of_pos c he hv (by omega)
    norm_num [evenCellClock, evenCellDeficit, he, hv, rr, sr, er, vr, rl, sl, el, vl]
    omega

private theorem clock_01 {m : Parameter} (c : Cell m) (he : c.e = 0) (hv : c.v = 1) :
    (evenCellClock (incomingCell c 0) < evenCellClock c ∨
      evenCellClock (incomingCell c 1) < evenCellClock c) ∧
    (evenCellDeficit c = 1 → evenCellClock (incomingCell c 0) < evenCellClock c ∧
      evenCellClock (incomingCell c 1) < evenCellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨ru, su, eu, vu⟩ := incomingCell_01_up c he hv
  by_cases hTop : c.r = m.val + 1
  · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_down_top c he hv hTop
    norm_num [evenCellClock, evenCellDeficit, he, hv, ru, su, eu, vu, rd, sd, ed, vd, hTop]
    omega
  · by_cases hEnd : c.r = m.val ∧ c.s = m.val - 1
    · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_down_penultimate c he hv hEnd.1 hEnd.2
      norm_num [evenCellClock, evenCellDeficit, he, hv, ru, su, eu, vu, rd, sd, ed, vd, hEnd.1, hEnd.2]
      omega
    · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_down_inner c he hv (by omega) hEnd
      norm_num [evenCellClock, evenCellDeficit, he, hv, ru, su, eu, vu, rd, sd, ed, vd]
      omega

private theorem clock_10 {m : Parameter} (c : Cell m) (he : c.e = 1) (hv : c.v = 0)
    (hNotPin : ¬evenCellPrescribed c) :
    (evenCellClock (incomingCell c 0) < evenCellClock c ∨
      evenCellClock (incomingCell c 1) < evenCellClock c) ∧
    (evenCellDeficit c = 1 → evenCellClock (incomingCell c 0) < evenCellClock c ∧
      evenCellClock (incomingCell c 1) < evenCellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hPin : ¬(c.r = 1 ∧ c.s = 1) := by
    intro h
    exact hNotPin ⟨h.1, h.2, he, hv⟩
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_10_down c he hv
  by_cases hr : c.r = 0
  · by_cases hs : c.s = 0
    · obtain ⟨ru, su, eu, vu⟩ := incomingCell_10_up_origin c he hv hr hs
      norm_num [evenCellClock, evenCellDeficit, he, hv, rd, sd, ed, vd, ru, su, eu, vu, hr, hs]
    · obtain ⟨ru, su, eu, vu⟩ := incomingCell_10_up_row_zero c he hv hr (by omega)
      norm_num [evenCellClock, evenCellDeficit, he, hv, rd, sd, ed, vd, ru, su, eu, vu, hr]
      omega
  · obtain ⟨ru, su, eu, vu⟩ := incomingCell_10_up_of_pos c he hv (by omega)
    norm_num [evenCellClock, evenCellDeficit, he, hv, rd, sd, ed, vd, ru, su, eu, vu]
    omega

private theorem clock_11 {m : Parameter} (c : Cell m) (he : c.e = 1) (hv : c.v = 1) :
    (evenCellClock (incomingCell c 0) < evenCellClock c ∨
      evenCellClock (incomingCell c 1) < evenCellClock c) ∧
    (evenCellDeficit c = 1 → evenCellClock (incomingCell c 0) < evenCellClock c ∧
      evenCellClock (incomingCell c 1) < evenCellClock c) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rl, sl, el, vl⟩ := incomingCell_11_left c he hv
  by_cases hLast : c.s = m.val - 1
  · obtain ⟨rr, sr, er, vr⟩ := incomingCell_11_right_last c he hv hLast
    norm_num [evenCellClock, evenCellDeficit, he, hv, rl, sl, el, vl, rr, sr, er, vr, hLast]
    omega
  · by_cases hEnd : c.r = m.val + 1 ∧ c.s = m.val - 2
    · obtain ⟨rr, sr, er, vr⟩ := incomingCell_11_right_top_endpoint c he hv hEnd.1 hEnd.2
      norm_num [evenCellClock, evenCellDeficit, he, hv, rl, sl, el, vl, rr, sr, er, vr, hEnd.1, hEnd.2]
      omega
    · obtain ⟨rr, sr, er, vr⟩ := incomingCell_11_right_inner c he hv (by omega) hEnd
      norm_num [evenCellClock, evenCellDeficit, he, hv, rl, sl, el, vl, rr, sr, er, vr]
      omega

/-- Every nonpin cell has one decreasing incoming clock, or both when its
actual profile deficit is one. -/
theorem evenCellClock_decreasing_inputs {m : Parameter} (c : Cell m)
    (hNotPin : ¬evenCellPrescribed c) :
    (evenCellClock (incomingCell c 0) < evenCellClock c ∨
      evenCellClock (incomingCell c 1) < evenCellClock c) ∧
    (evenCellDeficit c = 1 → evenCellClock (incomingCell c 0) < evenCellClock c ∧
      evenCellClock (incomingCell c 1) < evenCellClock c) := by
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · exact clock_00 c he hv
  · exact clock_01 c he hv
  · exact clock_10 c he hv hNotPin
  · exact clock_11 c he hv

/-- Strictly more actual incoming indices lower the clock than the literal
physical deficit. Index multiplicities are retained. -/
theorem even_cell_clock_selected {m : Parameter} (c : Cell m)
    (hNotPin : ¬evenCellPrescribed c) :
    ∃ S : Finset (Fin 2), incomingDeficit m 0 c.x c.y < (S.card : ℤ) ∧
      ∀ i ∈ S, evenCellClock (incomingCell c i) < evenCellClock c := by
  obtain ⟨hOne, hBoth⟩ := evenCellClock_decreasing_inputs c hNotPin
  rw [even_incomingDeficit_at_cell]
  rcases evenCellDeficit_zero_or_one c with hZero | hUnit
  · rcases hOne with hLeft | hRight
    · refine ⟨{0}, ?_, ?_⟩
      · simp only [hZero, Finset.card_singleton, Nat.cast_one, zero_lt_one]
      · intro i hi
        simpa only [Finset.mem_singleton.mp hi] using hLeft
    · refine ⟨{1}, ?_, ?_⟩
      · simp only [hZero, Finset.card_singleton, Nat.cast_one, zero_lt_one]
      · intro i hi
        simpa only [Finset.mem_singleton.mp hi] using hRight
  · obtain ⟨hLeft, hRight⟩ := hBoth hUnit
    refine ⟨Finset.univ, ?_, ?_⟩
    · norm_num [hUnit]
    · intro i _
      fin_cases i
      · exact hLeft
      · exact hRight

end FLattice.Auxiliary.MinusProfile
