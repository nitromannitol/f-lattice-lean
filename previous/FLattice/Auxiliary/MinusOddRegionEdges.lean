import FLattice.Auxiliary.MinusOddRegions
import Mathlib.Data.Fintype.Fin

/-!
# Actual incoming selections for the three odd-minus regions

Indices select physical incoming edges before representative decoding.
The first and third regions use right/vertical directions; the second
uses left/vertical directions. Earlier-region and prescribed exits are
retained explicitly. No periodicity of an unknown function is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile PlusOddProfile

/-- The first path always takes down or right, reaching its next path cell or the pin. -/
theorem oddRegionA_step {m : Parameter} (c : Cell m) (hc : oddRegionA c) :
    ∃ i : Fin 2, (c.e = c.v ∨ i = 1) ∧
      (oddCellPrescribed (incomingCell c i) ∨ oddRegionA (incomingCell c i)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · have hc' := hc
    norm_num [oddRegionA, oddColumn, he, hv] at hc'
    have hr : c.r ≤ m.val := by omega
    have hEnd : ¬(c.r = m.val ∧ c.s = m.val - 1) := by omega
    obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_inner c he hv hr hEnd
    refine ⟨0, Or.inl (he.trans hv.symm), ?_⟩
    norm_num [oddCellPrescribed, oddRegionA, oddColumn, rd, sd, ed, vd]
    omega
  · refine ⟨1, Or.inr rfl, ?_⟩
    have hc' := hc
    norm_num [oddRegionA, oddColumn, he, hv] at hc'
    by_cases hs : c.s = m.val - 1
    · obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_right_last c he hv hs
      norm_num [oddCellPrescribed, oddRegionA, oddColumn, rd, sd, ed, vd]
      omega
    · have hEnd : ¬(c.r = m.val + 1 ∧ c.s = m.val - 2) := by omega
      obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_right_inner c he hv (by omega) hEnd
      norm_num [oddCellPrescribed, oddRegionA, oddColumn, rd, sd, ed, vd]
      omega
  · refine ⟨1, Or.inr rfl, ?_⟩
    have hc' := hc
    norm_num [oddRegionA, oddColumn, he, hv] at hc'
    obtain ⟨rd, sd, ed, vd⟩ := incomingCell_10_right c he hv
    norm_num [oddCellPrescribed, oddRegionA, oddColumn, rd, sd, ed, vd]
    omega
  · refine ⟨0, Or.inl (he.trans hv.symm), ?_⟩
    have hc' := hc
    norm_num [oddRegionA, oddColumn, he, hv] at hc'
    obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_down c he hv
    norm_num [oddCellPrescribed, oddRegionA, oddColumn, rd, sd, ed, vd]
    omega

private theorem regionB_step_00_up {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) 
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_up c he hv 
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_00_down_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r ≤ m.val)
    (hEnd : ¬(c.r = m.val ∧ c.s = m.val - 1))
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_inner c he hv hr hEnd
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_00_down_penultimate {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = m.val) (hs : c.s = m.val - 1)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_penultimate c he hv hr hs
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr, hs] at _hc _hSelected ⊢

private theorem regionB_step_00_down_top {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hr : c.r = m.val + 1)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_00_down_top c he hv hr
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr] at _hc _hSelected ⊢

private theorem regionB_step_01_left {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) 
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_left c he hv 
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_01_right_inner {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hs : c.s ≤ m.val - 2)
    (hEnd : ¬(c.r = m.val + 1 ∧ c.s = m.val - 2))
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_right_inner c he hv hs hEnd
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hs] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_01_right_last {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hs : c.s = m.val - 1)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hZero : oddCellDeficit c = 0 := by
    norm_num [oddCellDeficit, he, hv, hs]
  rw [hZero] at _hSelected
  norm_num at _hSelected

private theorem regionB_step_01_right_top_endpoint {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hr : c.r = m.val + 1) (hs : c.s = m.val - 2)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_right_top_endpoint c he hv hr hs
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr, hs] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_10_right {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) 
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  simp [oddCellDeficit, he, hv] at _hSelected

private theorem regionB_step_10_left_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hs : 1 ≤ c.s)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_10_left_of_pos c he hv hs
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hs] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_10_left_of_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hs : c.s = 0) (hr : 1 ≤ c.r)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_10_left_of_zero c he hv hs hr
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hs, hr] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_10_left_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hr : c.r = 0) (hs : c.s = 0)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_10_left_origin c he hv hr hs
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr, hs] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_11_down {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) 
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (0 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 0) ∨ oddRegionA (incomingCell c 0) ∨
      (oddRegionB (incomingCell c 0) ∧ (c.e = c.v ∨ (0 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_down c he hv 
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_11_up_of_pos {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : 1 ≤ c.r)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_up_of_pos c he hv hr
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_11_up_origin {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = 0) (hs : c.s = 0)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_up_origin c he hv hr hs
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr, hs] at _hc _hSelected ⊢
  all_goals omega

private theorem regionB_step_11_up_row_zero {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hr : c.r = 0) (hs : 1 ≤ c.s)
    (_hc : oddRegionB c) (_hSelected : oddCellDeficit c = 1 ∨ (1 : Fin 2) = 0) :
    oddCellPrescribed (incomingCell c 1) ∨ oddRegionA (incomingCell c 1) ∨
      (oddRegionB (incomingCell c 1) ∧ (c.e = c.v ∨ (1 : Fin 2) = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_11_up_row_zero c he hv hr hs
  norm_num [oddCellPrescribed, oddRegionA, oddRegionB, oddColumn,
    oddCellDeficit, he, hv, rd, sd, ed, vd, hr, hs] at _hc _hSelected ⊢
  all_goals omega

/-- Every required second-region input either is prescribed, enters the first
region, or stays in the second with the left/vertical direction. -/
theorem oddRegionB_step {m : Parameter} (c : Cell m) (hc : oddRegionB c)
    (i : Fin 2) (hSelected : oddCellDeficit c = 1 ∨ i = 0) :
    oddCellPrescribed (incomingCell c i) ∨ oddRegionA (incomingCell c i) ∨
      (oddRegionB (incomingCell c i) ∧ (c.e = c.v ∨ i = 0)) := by
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv <;>
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · by_cases ht : c.r = m.val + 1
    · exact regionB_step_00_down_top c he hv ht hc hSelected
    · by_cases hend : c.r = m.val ∧ c.s = m.val - 1
      · exact regionB_step_00_down_penultimate c he hv hend.1 hend.2 hc hSelected
      · exact regionB_step_00_down_inner c he hv (by omega) hend hc hSelected
  · exact regionB_step_00_up c he hv hc hSelected
  · exact regionB_step_01_left c he hv hc hSelected
  · by_cases hs : c.s = m.val - 1
    · exact regionB_step_01_right_last c he hv hs hc hSelected
    · by_cases hend : c.r = m.val + 1 ∧ c.s = m.val - 2
      · exact regionB_step_01_right_top_endpoint c he hv hend.1 hend.2 hc hSelected
      · exact regionB_step_01_right_inner c he hv (by omega) hend hc hSelected
  · by_cases hs : c.s = 0
    · by_cases hr : c.r = 0
      · exact regionB_step_10_left_origin c he hv hr hs hc hSelected
      · exact regionB_step_10_left_of_zero c he hv hs (by omega) hc hSelected
    · exact regionB_step_10_left_of_pos c he hv (by omega) hc hSelected
  · exact regionB_step_10_right c he hv hc hSelected
  · exact regionB_step_11_down c he hv hc hSelected
  · by_cases hr : c.r = 0
    · by_cases hs : c.s = 0
      · exact regionB_step_11_up_origin c he hv hr hs hc hSelected
      · exact regionB_step_11_up_row_zero c he hv hr (by omega) hc hSelected
    · exact regionB_step_11_up_of_pos c he hv (by omega) hc hSelected

/-- The only horizontal black states left in the complement have their
left input in one of the two earlier regions. -/
theorem oddRegionC_black_left {m : Parameter} (c : Cell m) (hc : oddRegionC c)
    (hBlack : oddCellDeficit c = 1) (hHorizontal : c.e ≠ c.v) :
    oddRegionA (incomingCell c 0) ∨ oddRegionB (incomingCell c 0) := by
  obtain ⟨he, hv, hs, hr⟩ :=
    (oddCellDeficit_horizontal_eq_one_iff c hHorizontal).mp hBlack
  have hm := m.property
  have hr0 := c.hr0
  have hNotB := hc.2.2
  obtain ⟨rd, sd, ed, vd⟩ := incomingCell_01_left c he hv
  norm_num [oddRegionB, oddColumn, he, hv, hs] at hNotB
  norm_num [oddRegionA, oddRegionB, oddColumn, rd, sd, ed, vd, hs]
  omega

/-- Every required complement input enters a prior region or the prescribed
class, or remains in the complement with the right/vertical direction. -/
theorem oddRegionC_step {m : Parameter} (c : Cell m) (hc : oddRegionC c)
    (i : Fin 2) (hSelected : oddCellDeficit c = 1 ∨ i = 1) :
    oddCellPrescribed (incomingCell c i) ∨ oddRegionA (incomingCell c i) ∨
      oddRegionB (incomingCell c i) ∨
      (oddRegionC (incomingCell c i) ∧ (c.e = c.v ∨ i = 1)) := by
  by_cases hDirection : c.e = c.v ∨ i = 1
  · rcases odd_region_cover (incomingCell c i) with hp | ha | hb | hd
    · exact Or.inl hp
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr ⟨hd, hDirection⟩))
  · have hi : i = 0 := by
      have hine : i ≠ 1 := fun h => hDirection (Or.inr h)
      omega
    have hHorizontal : c.e ≠ c.v := fun h => hDirection (Or.inl h)
    have hBlack : oddCellDeficit c = 1 := by
      rcases hSelected with h | h
      · exact h
      · exact False.elim (hDirection (Or.inr h))
    subst i
    rcases oddRegionC_black_left c hc hBlack hHorizontal with ha | hb
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl hb))

/-- Enough actual incoming indices leave the first region in its permitted direction. -/
theorem oddRegionA_selected {m : Parameter} (c : Cell m) (hc : oddRegionA c) :
    ∃ S : Finset (Fin 2), oddCellDeficit c < (S.card : ℤ) ∧
      ∀ i ∈ S, oddCellPrescribed (incomingCell c i) ∨
        (oddRegionA (incomingCell c i) ∧ (c.e = c.v ∨ i = 1)) := by
  obtain ⟨i, hDir, hMove⟩ := oddRegionA_step c hc
  refine ⟨{i}, ?_, ?_⟩
  · rw [oddRegionA_deficit_zero c hc]
    norm_num
  · intro j hj
    have hji : j = i := by simpa using hj
    subst j
    rcases hMove with hp | ha
    · exact Or.inl hp
    · exact Or.inr ⟨ha, hDir⟩

/-- Enough second-region inputs enter a pin/prior region or descend left/vertically. -/
theorem oddRegionB_selected {m : Parameter} (c : Cell m) (hc : oddRegionB c) :
    ∃ S : Finset (Fin 2), oddCellDeficit c < (S.card : ℤ) ∧
      ∀ i ∈ S, oddCellPrescribed (incomingCell c i) ∨ oddRegionA (incomingCell c i) ∨
        (oddRegionB (incomingCell c i) ∧ (c.e = c.v ∨ i = 0)) := by
  rcases oddCellDeficit_zero_or_one c with hZero | hOne
  · refine ⟨{0}, ?_, ?_⟩
    · rw [hZero]; norm_num
    · intro i hi
      have hiZero : i = 0 := by simpa using hi
      exact oddRegionB_step c hc i (Or.inr hiZero)
  · refine ⟨Finset.univ, ?_, ?_⟩
    · rw [hOne]; norm_num
    · intro i _
      exact oddRegionB_step c hc i (Or.inl hOne)

/-- Enough complement inputs enter a pin/prior region or descend right/vertically. -/
theorem oddRegionC_selected {m : Parameter} (c : Cell m) (hc : oddRegionC c) :
    ∃ S : Finset (Fin 2), oddCellDeficit c < (S.card : ℤ) ∧
      ∀ i ∈ S, oddCellPrescribed (incomingCell c i) ∨ oddRegionA (incomingCell c i) ∨
        oddRegionB (incomingCell c i) ∨
        (oddRegionC (incomingCell c i) ∧ (c.e = c.v ∨ i = 1)) := by
  rcases oddCellDeficit_zero_or_one c with hZero | hOne
  · refine ⟨{1}, ?_, ?_⟩
    · rw [hZero]; norm_num
    · intro i hi
      have hiOne : i = 1 := by simpa using hi
      exact oddRegionC_step c hc i (Or.inr hiOne)
  · refine ⟨Finset.univ, ?_, ?_⟩
    · rw [hOne]; norm_num
    · intro i _
      exact oddRegionC_step c hc i (Or.inl hOne)

end FLattice.Auxiliary.MinusProfile
