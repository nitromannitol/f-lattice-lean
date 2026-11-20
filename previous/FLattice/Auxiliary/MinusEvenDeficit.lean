import FLattice.Auxiliary.MinusDeficit
import FLattice.Auxiliary.MinusEvenIncomingValues
import Mathlib.Tactic.SplitIfs

/-!
# Complete physical deficit table of the even-minus profile

The displayed table is derived from the actual incoming heights, including
all low rows and period seams. It is not a hypothesis. Period invariance
then proves the zero-or-one conclusion everywhere on the integer plane.
The odd-minus profile and the separately treated parameter m=1 are outside
this module's scope.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The source's complete even-minus cell table, with both low-row overrides. -/
def evenCellDeficit {m : Parameter} (c : Cell m) : ℤ :=
  if c.r = 0 then
    if c.e = 0 then 0 else if c.v = 0 then (if 1 ≤ c.s then 1 else 0)
    else (if c.s = 0 then 1 else 0)
  else if c.r = 1 then
    if c.e = 0 then (if c.v = 0 then 0 else if 1 ≤ c.s then 1 else 0)
    else if c.v = 0 then 1 else 0
  else if c.e = 0 then
    if c.v = 0 then (if c.s = 0 ∨ c.r - c.s = 1 then 1 else 0)
    else (if c.r - c.s ≠ 1 ∧ c.r - c.s ≠ 2 then 1 else 0)
  else if c.v = 0 then
    (if (c.r - c.s ≠ 1 ∧ c.r - c.s ≠ 2) ∨ (c.r = 2 ∧ c.s = 0) then 1 else 0)
  else (if c.r - c.s = 2 then 1 else 0)

private theorem deficit_at_cell_inputs {m : Parameter} (c : Cell m) :
    incomingDeficit m 0 c.x c.y = 2 * representativeHeight m 0 c -
      profile m 0 (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 -
      profile m 0 (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 := by
  rw [← profile_at_cell m 0 c]
  by_cases hp : (c.x + c.y) % 2 = 0 <;>
    simp [incomingDeficit, incomingPoint, hp, sub_eq_add_neg]

private theorem deficit_00 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) :
    incomingDeficit m 0 c.x c.y = evenCellDeficit c := by
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
  rw [deficit_at_cell_inputs, even_profile_incoming_00_right c he hv]
  obtain ⟨rr, sr, er, vr⟩ := incomingCell_00_right c he hv
  by_cases hs : c.s = 0
  · by_cases hr : c.r = 0
    · rw [even_profile_incoming_00_left_origin c he hv hr hs]
      obtain ⟨rl, sl, el, vl⟩ := incomingCell_00_left_origin c he hv hr hs
      norm_num [representativeHeight, evenCellDeficit, he, hv, hr, hs,
        rr, sr, er, vr, rl, sl, el, vl]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [even_profile_incoming_00_left_of_zero c he hv hs (by omega)]
      obtain ⟨rl, sl, el, vl⟩ := incomingCell_00_left_of_zero c he hv hs (by omega)
      norm_num [representativeHeight, evenCellDeficit, he, hv, hs,
        rr, sr, er, vr, rl, sl, el, vl]
      split_ifs <;> ring_nf
      all_goals omega
  · rw [even_profile_incoming_00_left_of_pos c he hv (by omega)]
    obtain ⟨rl, sl, el, vl⟩ := incomingCell_00_left_of_pos c he hv (by omega)
    norm_num [representativeHeight, evenCellDeficit, he, hv,
      rr, sr, er, vr, rl, sl, el, vl]
    split_ifs <;> ring_nf
    all_goals omega

private theorem deficit_01 {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) :
    incomingDeficit m 0 c.x c.y = evenCellDeficit c := by
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
  rw [deficit_at_cell_inputs, even_profile_incoming_01_up c he hv]
  obtain ⟨ru, su, eu, vu⟩ := incomingCell_01_up c he hv
  by_cases hTop : c.r = m.val + 1
  · rw [even_profile_incoming_01_down_top c he hv hTop]
    obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_down_top c he hv hTop
    norm_num [representativeHeight, evenCellDeficit, he, hv, hTop,
      ru, su, eu, vu, rd, sd, ed, vd]
    split_ifs <;> ring_nf
    all_goals omega
  · by_cases hEnd : c.r = m.val ∧ c.s = m.val - 1
    · rw [even_profile_incoming_01_down_penultimate c he hv hEnd.1 hEnd.2]
      obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_down_penultimate c he hv hEnd.1 hEnd.2
      norm_num [representativeHeight, evenCellDeficit, he, hv, hEnd.1, hEnd.2,
        ru, su, eu, vu, rd, sd, ed, vd]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [even_profile_incoming_01_down_inner c he hv (by omega) hEnd]
      obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_down_inner c he hv (by omega) hEnd
      norm_num [representativeHeight, evenCellDeficit, he, hv,
        ru, su, eu, vu, rd, sd, ed, vd]
      split_ifs <;> ring_nf
      all_goals omega

private theorem deficit_10 {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) :
    incomingDeficit m 0 c.x c.y = evenCellDeficit c := by
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
  rw [deficit_at_cell_inputs, even_profile_incoming_10_down c he hv]
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_10_down c he hv
  by_cases hr : c.r = 0
  · by_cases hs : c.s = 0
    · rw [even_profile_incoming_10_up_origin c he hv hr hs]
      obtain ⟨ru, su, eu, vu⟩ := incomingCell_10_up_origin c he hv hr hs
      norm_num [representativeHeight, evenCellDeficit, he, hv, hr, hs,
        rd, sd, ed, vd, ru, su, eu, vu]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [even_profile_incoming_10_up_row_zero c he hv hr (by omega)]
      obtain ⟨ru, su, eu, vu⟩ := incomingCell_10_up_row_zero c he hv hr (by omega)
      norm_num [representativeHeight, evenCellDeficit, he, hv, hr,
        rd, sd, ed, vd, ru, su, eu, vu]
      split_ifs <;> ring_nf
      all_goals omega
  · rw [even_profile_incoming_10_up_of_pos c he hv (by omega)]
    obtain ⟨ru, su, eu, vu⟩ := incomingCell_10_up_of_pos c he hv (by omega)
    norm_num [representativeHeight, evenCellDeficit, he, hv,
      rd, sd, ed, vd, ru, su, eu, vu]
    split_ifs <;> ring_nf
    all_goals omega

private theorem deficit_11 {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) :
    incomingDeficit m 0 c.x c.y = evenCellDeficit c := by
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
  rw [deficit_at_cell_inputs, even_profile_incoming_11_left c he hv]
  obtain ⟨rl, sl, el, vl⟩ := incomingCell_11_left c he hv
  by_cases hs : c.s = m.val - 1
  · rw [even_profile_incoming_11_right_last c he hv hs]
    obtain ⟨rr, sr, er, vr⟩ := incomingCell_11_right_last c he hv hs
    norm_num [representativeHeight, evenCellDeficit, he, hv, hs,
      rl, sl, el, vl, rr, sr, er, vr]
    split_ifs <;> ring_nf
    all_goals omega
  · by_cases hEnd : c.r = m.val + 1 ∧ c.s = m.val - 2
    · rw [even_profile_incoming_11_right_top_endpoint c he hv hEnd.1 hEnd.2]
      obtain ⟨rr, sr, er, vr⟩ := incomingCell_11_right_top_endpoint c he hv hEnd.1 hEnd.2
      norm_num [representativeHeight, evenCellDeficit, he, hv, hEnd.1, hEnd.2,
        rl, sl, el, vl, rr, sr, er, vr]
      split_ifs <;> ring_nf
      all_goals omega
    · rw [even_profile_incoming_11_right_inner c he hv (by omega) hEnd]
      obtain ⟨rr, sr, er, vr⟩ := incomingCell_11_right_inner c he hv (by omega) hEnd
      norm_num [representativeHeight, evenCellDeficit, he, hv,
        rl, sl, el, vl, rr, sr, er, vr]
      split_ifs <;> ring_nf
      all_goals omega

/-- The complete even-minus table is the actual physical deficit of every valid Cell. -/
theorem even_incomingDeficit_at_cell {m : Parameter} (c : Cell m) :
    incomingDeficit m 0 c.x c.y = evenCellDeficit c := by
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · exact deficit_00 c he hv
  · exact deficit_01 c he hv
  · exact deficit_10 c he hv
  · exact deficit_11 c he hv

/-- Every displayed even-minus deficit is zero or one, with no excluded cell. -/
theorem evenCellDeficit_zero_or_one {m : Parameter} (c : Cell m) :
    evenCellDeficit c = 0 ∨ evenCellDeficit c = 1 := by
  unfold evenCellDeficit
  split_ifs <;> omega

/-- The complete physical table at an arbitrary signed lattice point. -/
theorem even_incomingDeficit_eq_cellTable (m : Parameter) (x y : ℤ) :
    incomingDeficit m 0 x y = evenCellDeficit (cellOf m x y) := by
  rw [incomingDeficit_eq_cellOf, even_incomingDeficit_at_cell]

/-- The literal even-minus profile has deficit zero or one at every physical point. -/
theorem even_incomingDeficit_zero_or_one (m : Parameter) (x y : ℤ) :
    incomingDeficit m 0 x y = 0 ∨ incomingDeficit m 0 x y = 1 := by
  rw [even_incomingDeficit_eq_cellTable]
  exact evenCellDeficit_zero_or_one (cellOf m x y)

end FLattice.Auxiliary.MinusProfile
