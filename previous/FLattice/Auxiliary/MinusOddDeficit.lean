import FLattice.Auxiliary.MinusDeficit
import FLattice.Auxiliary.MinusOddIncomingValues
import Mathlib.Tactic.SplitIfs

/-!
# Complete physical deficit table of the odd-minus profile

The actual odd-native incoming heights give the complete table on exact
Cells, including the row-zero override and every wrapped edge. Signed
period invariance then gives the table everywhere. All deficits are zero
or one, even on the prescribed class; the prescribed coset is identified
separately by coordinates. No comparison or recurrence is asserted.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile PlusOddProfile

/-- The source's complete odd-minus table, with its row-zero override. -/
def oddCellDeficit {m : Parameter} (c : Cell m) : ℤ :=
  if c.r = 0 then
    if c.e = 0 then
      if c.v = 0 then (if c.s ≤ m.val - 2 then 1 else 0)
      else (if c.s = m.val - 2 then 1 else 0)
    else if c.v = 0 then 0 else (if c.s = m.val - 1 then 1 else 0)
  else if c.e = 0 then
    if c.v = 0 then 1 - (if c.r - c.s = 2 then 1 else 0)
    else (if c.s = m.val - 2 ∧ c.r ≤ m.val then 1 else 0)
  else if c.v = 0 then 0
  else 1 - (if c.r - c.s = 3 then 1 else 0) -
    (if c.r = 1 ∧ c.s = m.val - 1 then 1 else 0)

private theorem deficit_at_cell_inputs {m : Parameter} (c : Cell m) :
    incomingDeficit m 1 c.x c.y = 2 * representativeHeight m 1 c -
      profile m 1 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 -
      profile m 1 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 := by
  rw [← profile_at_cell m 1 c]
  by_cases hp : (c.x + c.y + 1) % 2 = 0 <;>
    simp [incomingDeficit, incomingPoint, hp, sub_eq_add_neg]

private theorem deficit_00 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) :
    incomingDeficit m 1 c.x c.y = oddCellDeficit c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hSquareZero : c.r ≠ 0 ∨ c.r ^ 2 = 0 := by
    by_cases hr : c.r = 0
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareOne : c.r ≠ 1 ∨ c.r ^ 2 = 1 := by
    by_cases hr : c.r = 1
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareTwo : c.r ≠ 2 ∨ c.r ^ 2 = 4 := by
    by_cases hr : c.r = 2
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  rw [deficit_at_cell_inputs, odd_profile_incoming_00_up c he hv]
  obtain ⟨ru, su, eu, vu⟩ := incomingCell_00_up c he hv
  by_cases hTop : c.r = m.val + 1
  · rw [odd_profile_incoming_00_down_top c he hv hTop]
    obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_top c he hv hTop
    norm_num [representativeHeight, oddCellDeficit, he, hv, hTop,
      ru, su, eu, vu, rd, sd, ed, vd]
    split_ifs <;> ring_nf
    all_goals omega
  · by_cases hEnd : c.r = m.val ∧ c.s = m.val - 1
    · rw [odd_profile_incoming_00_down_penultimate c he hv hEnd.1 hEnd.2]
      obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_penultimate c he hv hEnd.1 hEnd.2
      norm_num [representativeHeight, oddCellDeficit, he, hv, hEnd.1, hEnd.2,
        ru, su, eu, vu, rd, sd, ed, vd]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [odd_profile_incoming_00_down_inner c he hv (by omega) hEnd]
      obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_inner c he hv (by omega) hEnd
      norm_num [representativeHeight, oddCellDeficit, he, hv,
        ru, su, eu, vu, rd, sd, ed, vd]
      split_ifs <;> ring_nf
      all_goals omega

private theorem deficit_01 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) :
    incomingDeficit m 1 c.x c.y = oddCellDeficit c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hSquareZero : c.r ≠ 0 ∨ c.r ^ 2 = 0 := by
    by_cases hr : c.r = 0
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareOne : c.r ≠ 1 ∨ c.r ^ 2 = 1 := by
    by_cases hr : c.r = 1
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareTwo : c.r ≠ 2 ∨ c.r ^ 2 = 4 := by
    by_cases hr : c.r = 2
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  rw [deficit_at_cell_inputs, odd_profile_incoming_01_left c he hv]
  obtain ⟨rl, sl, el, vl⟩ := incomingCell_01_left c he hv
  by_cases hs : c.s = m.val - 1
  · rw [odd_profile_incoming_01_right_last c he hv hs]
    obtain ⟨rr, sr, er, vr⟩ := incomingCell_01_right_last c he hv hs
    norm_num [representativeHeight, oddCellDeficit, he, hv, hs,
      rl, sl, el, vl, rr, sr, er, vr]
    split_ifs <;> ring_nf
    all_goals omega
  · by_cases hEnd : c.r = m.val + 1 ∧ c.s = m.val - 2
    · rw [odd_profile_incoming_01_right_top_endpoint c he hv hEnd.1 hEnd.2]
      obtain ⟨rr, sr, er, vr⟩ := incomingCell_01_right_top_endpoint c he hv hEnd.1 hEnd.2
      norm_num [representativeHeight, oddCellDeficit, he, hv, hEnd.1, hEnd.2,
        rl, sl, el, vl, rr, sr, er, vr]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [odd_profile_incoming_01_right_inner c he hv (by omega) hEnd]
      obtain ⟨rr, sr, er, vr⟩ := incomingCell_01_right_inner c he hv (by omega) hEnd
      norm_num [representativeHeight, oddCellDeficit, he, hv,
        rl, sl, el, vl, rr, sr, er, vr]
      split_ifs <;> ring_nf
      all_goals omega

private theorem deficit_10 {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) :
    incomingDeficit m 1 c.x c.y = oddCellDeficit c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hSquareZero : c.r ≠ 0 ∨ c.r ^ 2 = 0 := by
    by_cases hr : c.r = 0
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareOne : c.r ≠ 1 ∨ c.r ^ 2 = 1 := by
    by_cases hr : c.r = 1
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareTwo : c.r ≠ 2 ∨ c.r ^ 2 = 4 := by
    by_cases hr : c.r = 2
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  rw [deficit_at_cell_inputs, odd_profile_incoming_10_right c he hv]
  obtain ⟨rr, sr, er, vr⟩ := incomingCell_10_right c he hv
  by_cases hs : c.s = 0
  · by_cases hr : c.r = 0
    · rw [odd_profile_incoming_10_left_origin c he hv hr hs]
      obtain ⟨rl, sl, el, vl⟩ := incomingCell_10_left_origin c he hv hr hs
      norm_num [representativeHeight, oddCellDeficit, he, hv, hr, hs,
        rr, sr, er, vr, rl, sl, el, vl]
      split_ifs <;> ring_nf
    · rw [odd_profile_incoming_10_left_of_zero c he hv hs (by omega)]
      obtain ⟨rl, sl, el, vl⟩ := incomingCell_10_left_of_zero c he hv hs (by omega)
      norm_num [representativeHeight, oddCellDeficit, he, hv, hs,
        rr, sr, er, vr, rl, sl, el, vl]
      split_ifs <;> ring_nf
      all_goals omega
  · rw [odd_profile_incoming_10_left_of_pos c he hv (by omega)]
    obtain ⟨rl, sl, el, vl⟩ := incomingCell_10_left_of_pos c he hv (by omega)
    norm_num [representativeHeight, oddCellDeficit, he, hv,
      rr, sr, er, vr, rl, sl, el, vl]
    split_ifs <;> ring_nf
    all_goals omega

private theorem deficit_11 {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) :
    incomingDeficit m 1 c.x c.y = oddCellDeficit c := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  have hSquareZero : c.r ≠ 0 ∨ c.r ^ 2 = 0 := by
    by_cases hr : c.r = 0
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareOne : c.r ≠ 1 ∨ c.r ^ 2 = 1 := by
    by_cases hr : c.r = 1
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  have hSquareTwo : c.r ≠ 2 ∨ c.r ^ 2 = 4 := by
    by_cases hr : c.r = 2
    · right; rw [hr]; norm_num
    · exact Or.inl hr
  rw [deficit_at_cell_inputs, odd_profile_incoming_11_down c he hv]
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_down c he hv
  by_cases hr : c.r = 0
  · by_cases hs : c.s = 0
    · rw [odd_profile_incoming_11_up_origin c he hv hr hs]
      obtain ⟨ru, su, eu, vu⟩ := incomingCell_11_up_origin c he hv hr hs
      norm_num [representativeHeight, oddCellDeficit, he, hv, hr, hs,
        rd, sd, ed, vd, ru, su, eu, vu]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [odd_profile_incoming_11_up_row_zero c he hv hr (by omega)]
      obtain ⟨ru, su, eu, vu⟩ := incomingCell_11_up_row_zero c he hv hr (by omega)
      norm_num [representativeHeight, oddCellDeficit, he, hv, hr,
        rd, sd, ed, vd, ru, su, eu, vu]
      split_ifs <;> ring_nf
      all_goals omega
  · rw [odd_profile_incoming_11_up_of_pos c he hv (by omega)]
    obtain ⟨ru, su, eu, vu⟩ := incomingCell_11_up_of_pos c he hv (by omega)
    norm_num [representativeHeight, oddCellDeficit, he, hv,
      rd, sd, ed, vd, ru, su, eu, vu]
    split_ifs <;> ring_nf
    all_goals omega

/-- The complete odd-minus table equals the actual deficit at every valid representative. -/
theorem odd_incomingDeficit_at_cell {m : Parameter} (c : Cell m) :
    incomingDeficit m 1 c.x c.y = oddCellDeficit c := by
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · exact deficit_00 c he hv
  · exact deficit_01 c he hv
  · exact deficit_10 c he hv
  · exact deficit_11 c he hv

/-- The odd-minus table is binary on all cells, including its prescribed cell. -/
theorem oddCellDeficit_zero_or_one {m : Parameter} (c : Cell m) :
    oddCellDeficit c = 0 ∨ oddCellDeficit c = 1 := by
  have hm := m.property
  have hs0 := c.hs0
  unfold oddCellDeficit
  split_ifs <;> omega

/-- The complete physical table at an arbitrary signed lattice point. -/
theorem odd_incomingDeficit_eq_cellTable (m : Parameter) (x y : ℤ) :
    incomingDeficit m 1 x y = oddCellDeficit (cellOf m x y) := by
  rw [incomingDeficit_eq_cellOf, odd_incomingDeficit_at_cell]

/-- Every physical odd-minus deficit is zero or one, without a pin exception. -/
theorem odd_incomingDeficit_zero_or_one (m : Parameter) (x y : ℤ) :
    incomingDeficit m 1 x y = 0 ∨ incomingDeficit m 1 x y = 1 := by
  rw [odd_incomingDeficit_eq_cellTable]
  exact oddCellDeficit_zero_or_one (cellOf m x y)

/-- In particular the physical deficit lies between zero and one, also on the pin. -/
theorem odd_incomingDeficit_bounds (m : Parameter) (x y : ℤ) :
    0 ≤ incomingDeficit m 1 x y ∧ incomingDeficit m 1 x y ≤ 1 := by
  rcases odd_incomingDeficit_zero_or_one m x y with h | h <;> omega

/-- Among horizontal cells, deficit one occurs exactly on the source's short column. -/
theorem oddCellDeficit_horizontal_eq_one_iff {m : Parameter} (c : Cell m)
    (hHorizontal : c.e ≠ c.v) :
    oddCellDeficit c = 1 ↔
      c.e = 0 ∧ c.v = 1 ∧ c.s = m.val - 2 ∧ c.r ≤ m.val := by
  have hr0 := c.hr0
  have hm := m.property
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · exact False.elim (hHorizontal (he.trans hv.symm))
  · simp only [oddCellDeficit, he, hv]
    norm_num
    split_ifs <;> omega
  · simp [oddCellDeficit, he, hv]
  · exact False.elim (hHorizontal (he.trans hv.symm))

/-- The source's odd prescribed cell, independently of its deficit. -/
def oddCellPrescribed {m : Parameter} (c : Cell m) : Prop :=
  c.r = m.val + 1 ∧ c.s = m.val - 2 ∧ c.e = 0 ∧ c.v = 1

/-- The actual signed source coset D1-C(a,b), with D1=(-1,0). -/
def oddPrescribedCoset (m : Parameter) (x y : ℤ) : Prop :=
  ∃ a b : ℤ,
    x = -1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
    y = -2 * m.val * a - 2 * b

/-- The canonical prescribed-cell condition is exactly the signed source coset. -/
theorem oddCellPrescribed_cellOf_iff (m : Parameter) (x y : ℤ) :
    oddCellPrescribed (cellOf m x y) ↔ oddPrescribedCoset m x y := by
  constructor
  · rintro ⟨hr, hs, he, hv⟩
    obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
    simp only [Cell.x, Cell.y, hr, hs, he, hv] at hx hy
    norm_num at hx hy
    refine ⟨-q - 1, m.val * (q + 1) - k, ?_, ?_⟩
    · rw [hx]
      unfold halfPeriod
      ring
    · rw [hy]
      ring
  · rintro ⟨a, b, rfl, rfl⟩
    have hm := m.property
    let p : Cell m := ⟨m.val + 1, m.val - 2, 0, 1,
      by omega, by omega, by omega, by omega, by omega⟩
    have hLift := cellOf_lifted_cell m p (-m.val * a - b) (-a - 1)
    have hX : p.x + 2 * m.val * (-m.val * a - b) + 2 * halfPeriod m * (-a - 1) =
        -1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b := by
      dsimp [p, Cell.x, halfPeriod]
      ring
    have hY : 2 * (-m.val * a - b) + p.y = -2 * m.val * a - 2 * b := by
      dsimp [p, Cell.y]
      ring
    rw [hX, hY] at hLift
    rw [hLift]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The prescribed odd cell is white: its actual deficit is zero. -/
theorem oddCellDeficit_of_prescribed {m : Parameter} (c : Cell m)
    (h : oddCellPrescribed c) : oddCellDeficit c = 0 := by
  obtain ⟨hr, hs, he, hv⟩ := h
  have hm := m.property
  norm_num [oddCellDeficit, hr, hs, he, hv, show m.val + 1 ≠ 0 by omega,
    show ¬m.val + 1 ≤ m.val by omega]

/-- Every signed point of the source prescribed coset has actual deficit zero. -/
theorem odd_incomingDeficit_of_prescribed (m : Parameter) (x y : ℤ)
    (h : oddPrescribedCoset m x y) : incomingDeficit m 1 x y = 0 := by
  rw [odd_incomingDeficit_eq_cellTable]
  exact oddCellDeficit_of_prescribed (cellOf m x y)
    ((oddCellPrescribed_cellOf_iff m x y).mpr h)

/-- Literal signed-index form of the prescribed-coset deficit identity. -/
theorem odd_incomingDeficit_prescribed_coset (m : Parameter) (a b : ℤ) :
    incomingDeficit m 1
      (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b)
      (-2 * m.val * a - 2 * b) = 0 := by
  exact odd_incomingDeficit_of_prescribed m _ _ ⟨a, b, rfl, rfl⟩

end FLattice.Auxiliary.MinusProfile
