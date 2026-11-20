import FLattice.Auxiliary.PlusEvenCells
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# The four source regions on valid even-plus cells

Each predicate is the literal region table, restricted by the `Cell` carrier
to the representative domain. The prescribed class and all four regions form
an exclusive partition; no region label is assigned to invalid coordinates.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The prescribed representative `10(0,0)`. -/
def cellPrescribed {m : Parameter} (c : Cell m) : Prop :=
  c.r = 0 ∧ c.s = 0 ∧ c.e = 1 ∧ c.v = 0

/-- Region I, including the two additional boundary classes. -/
def regionI {m : Parameter} (c : Cell m) : Prop :=
  if c.e = 0 then
    if c.v = 0 then c.r = 0 ∨ (1 ≤ c.r ∧ c.r ≤ c.s)
    else c.r = 0 ∨ (1 ≤ c.r ∧ c.r - 1 ≤ c.s ∧ c.s ≤ m.val - 2) ∨
      (c.r = m.val + 1 ∧ c.s = m.val - 2)
  else if c.v = 0 then
    (c.r = 0 ∧ 1 ≤ c.s) ∨ (1 ≤ c.r ∧ c.r - 1 ≤ c.s)
  else (c.r = 0 ∧ 1 ≤ c.s) ∨
    (1 ≤ c.r ∧ c.r - 1 ≤ c.s ∧ c.s ≤ m.val - 2) ∨
    (c.r = 1 ∧ c.s = m.val - 1)

/-- The source's explicit description of Region II. -/
def regionII {m : Parameter} (c : Cell m) : Prop :=
  if c.e = 0 then
    if c.v = 0 then 1 ≤ c.r ∧ (c.r - c.s = 1 ∨ 3 ≤ c.r - c.s)
    else (c.s = m.val - 1 ∧ 1 ≤ c.r ∧ c.r ≤ m.val) ∨
      (3 ≤ c.r - c.s ∧ ¬(c.r = m.val + 1 ∧ c.s = m.val - 2))
  else if c.v = 0 then 3 ≤ c.r - c.s
  else (c.r = 0 ∧ c.s = 0) ∨
    (2 ≤ c.r ∧ (c.r - c.s = 2 ∨ 4 ≤ c.r - c.s)) ∨
    (c.s = m.val - 1 ∧ 2 ≤ c.r ∧ c.r ≤ m.val)

/-- Region III consists of the two connecting classes. -/
def regionIII {m : Parameter} (c : Cell m) : Prop :=
  (c.e = 0 ∧ c.v = 1 ∧ c.r = m.val ∧ c.s = m.val - 2) ∨
    (c.e = 1 ∧ c.v = 1 ∧ c.r = m.val + 1 ∧ c.s = m.val - 2)

/-- Region IV is the four-state diagonal specified in the source. -/
def regionIV {m : Parameter} (c : Cell m) : Prop :=
  if c.v = 0 then 2 ≤ c.r ∧ c.r ≤ m.val ∧ c.s = c.r - 2
  else if c.e = 0 then 2 ≤ c.r ∧ c.r ≤ m.val - 1 ∧ c.s = c.r - 2
  else 3 ≤ c.r ∧ c.r ≤ m.val ∧ c.s = c.r - 3

/-- The explicit Region II formula equals the complement stated in the source. -/
theorem regionII_iff_complement {m : Parameter} (c : Cell m) :
    regionII c ↔ ¬cellPrescribed c ∧ ¬regionI c ∧ ¬regionIII c ∧ ¬regionIV c := by
  rcases c with ⟨r, s, e, v, hr0, hrm, hs0, hsm, hMissing⟩
  have hm := m.property
  fin_cases e <;> fin_cases v <;>
    norm_num [regionII, cellPrescribed, regionI, regionIII, regionIV] <;> omega

/-- The prescribed class and the four regions cover all valid representatives. -/
theorem cell_region_cover {m : Parameter} (c : Cell m) :
    cellPrescribed c ∨ regionI c ∨ regionII c ∨ regionIII c ∨ regionIV c := by
  classical
  by_cases hP : cellPrescribed c
  · exact Or.inl hP
  by_cases hI : regionI c
  · exact Or.inr (Or.inl hI)
  by_cases hIII : regionIII c
  · exact Or.inr (Or.inr (Or.inr (Or.inl hIII)))
  by_cases hIV : regionIV c
  · exact Or.inr (Or.inr (Or.inr (Or.inr hIV)))
  exact Or.inr (Or.inr (Or.inl ((regionII_iff_complement c).mpr ⟨hP, hI, hIII, hIV⟩)))

/-- The noncomplement classes are pairwise disjoint, including both endpoints. -/
theorem cell_region_disjoint {m : Parameter} (c : Cell m) :
    (cellPrescribed c → ¬regionI c ∧ ¬regionIII c ∧ ¬regionIV c) ∧
      (regionI c → ¬regionIII c ∧ ¬regionIV c) ∧ (regionIII c → ¬regionIV c) := by
  rcases c with ⟨r, s, e, v, hr0, hrm, hs0, hsm, hMissing⟩
  have hm := m.property
  fin_cases e <;> fin_cases v <;>
    norm_num [cellPrescribed, regionI, regionIII, regionIV] <;> omega

end FLattice.Auxiliary.PlusEvenProfile
