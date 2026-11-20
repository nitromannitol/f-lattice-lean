import FLattice.Auxiliary.MinusOddDeficit

/-!
# The three source regions of the odd-minus comparison

All predicates are on the exact shared Cell carrier. The column is j=2s+v;
all physical lifts are handled by applying these predicates to `cellOf`.
The complement excludes the pin explicitly. No height comparison is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The literal full horizontal column within a row. -/
def oddColumn {m : Parameter} (c : Cell m) : ℤ := 2 * c.s + (c.v.val : ℤ)

/-- The first source region: the right-moving path and its four initial cells. -/
def oddRegionA {m : Parameter} (c : Cell m) : Prop :=
  (c.e = 0 ∧ 2 ≤ c.r ∧ c.r ≤ m.val ∧ oddColumn c = 2 * c.r - 4) ∨
  (c.e = 0 ∧ 3 ≤ c.r ∧ c.r ≤ m.val ∧ oddColumn c = 2 * c.r - 5) ∨
  (c.e = 1 ∧ 3 ≤ c.r ∧ c.r ≤ m.val + 1 ∧ oddColumn c = 2 * c.r - 6) ∨
  (c.e = 1 ∧ 3 ≤ c.r ∧ c.r ≤ m.val + 1 ∧ oddColumn c = 2 * c.r - 5) ∨
  (c.r = 0 ∧ oddColumn c = 2 * m.val - 2 ∧ c.e = 0) ∨
  (c.r = 1 ∧ oddColumn c = 2 * m.val - 2 ∧ c.e = 1) ∨
  (c.r = 1 ∧ oddColumn c = 2 * m.val - 1 ∧ c.e = 1) ∨
  (c.r = 1 ∧ oddColumn c = 2 * m.val - 1 ∧ c.e = 0)

/-- The second source region, with every low-row and top-row piece retained. -/
def oddRegionB {m : Parameter} (c : Cell m) : Prop :=
  (c.r = 0 ∧ c.e = 1) ∨
  (c.r = 0 ∧ c.e = 0 ∧ oddColumn c ≠ 2 * m.val - 2) ∨
  (c.r = 1 ∧ oddColumn c ≤ 2 * m.val - 4) ∨
  (2 ≤ c.r ∧ c.r ≤ m.val ∧ c.e = 0 ∧
    2 * c.r - 3 ≤ oddColumn c ∧ oddColumn c ≤ 2 * m.val - 4) ∨
  (2 ≤ c.r ∧ c.r ≤ m.val ∧ c.e = 1 ∧
    2 * c.r - 4 ≤ oddColumn c ∧ oddColumn c ≤ 2 * m.val - 4) ∨
  (c.r = m.val + 1 ∧ c.e = 0 ∧ oddColumn c = 2 * m.val - 4)

/-- The remaining source region, with the prescribed class removed. -/
def oddRegionC {m : Parameter} (c : Cell m) : Prop :=
  ¬oddCellPrescribed c ∧ ¬oddRegionA c ∧ ¬oddRegionB c

/-- The first path contains no prescribed cell. -/
theorem oddRegionA_not_prescribed {m : Parameter} (c : Cell m) (h : oddRegionA c) :
    ¬oddCellPrescribed c := by
  intro hp
  obtain ⟨hr, hs, he, hv⟩ := hp
  have hm := m.property
  norm_num [oddRegionA, oddColumn, hr, hs, he, hv] at h
  omega

/-- The second region contains no prescribed cell. -/
theorem oddRegionB_not_prescribed {m : Parameter} (c : Cell m) (h : oddRegionB c) :
    ¬oddCellPrescribed c := by
  intro hp
  obtain ⟨hr, hs, he, hv⟩ := hp
  have hm := m.property
  norm_num [oddRegionB, oddColumn, hr, hs, he, hv] at h
  omega

/-- The two explicitly listed regions are disjoint on every valid cell. -/
theorem oddRegionA_not_B {m : Parameter} (c : Cell m) (h : oddRegionA c) :
    ¬oddRegionB c := by
  intro hb
  have hm := m.property
  have hr0 := c.hr0
  have hrm := c.hrm
  have hs0 := c.hs0
  have hsm := c.hsm
  have hMissing := c.hMissing
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  all_goals norm_num [oddRegionA, oddRegionB, oddColumn, he, hv] at h hb
  all_goals omega

/-- The three regions and the prescribed class cover every valid cell. -/
theorem odd_region_cover {m : Parameter} (c : Cell m) :
    oddCellPrescribed c ∨ oddRegionA c ∨ oddRegionB c ∨ oddRegionC c := by
  classical
  by_cases hp : oddCellPrescribed c
  · exact Or.inl hp
  by_cases ha : oddRegionA c
  · exact Or.inr (Or.inl ha)
  by_cases hb : oddRegionB c
  · exact Or.inr (Or.inr (Or.inl hb))
  exact Or.inr (Or.inr (Or.inr ⟨hp, ha, hb⟩))

/-- Every cell of the first path has zero actual deficit. -/
theorem oddRegionA_deficit_zero {m : Parameter} (c : Cell m) (h : oddRegionA c) :
    oddCellDeficit c = 0 := by
  have hm := m.property
  have hs0 := c.hs0
  have hsm := c.hsm
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  all_goals norm_num [oddRegionA, oddColumn, he, hv] at h
  all_goals norm_num [oddCellDeficit, he, hv]
  all_goals split_ifs <;> omega

end FLattice.Auxiliary.MinusProfile
