import FLattice.Auxiliary.PlusEvenCells
import Mathlib.Tactic.SplitIfs

/-!
# Prescribed cell and displayed odd deficit table

The table combines the manuscript's two bottom rows, last column, pin pair,
and ordinary bulk formulas. Identifying it with the literal profile's
incoming deficit is a separate theorem, not a premise of this definition.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The displayed prescribed odd cell `01(m+1,m-2)`. -/
def cellPrescribed {m : Parameter} (c : Cell m) : Prop :=
  c.r = m.val + 1 ∧ c.s = m.val - 2 ∧ c.e = 0 ∧ c.v = 1

/-- The source's complete displayed table, prior to proving its physical identity. -/
def cellDeficitTable {m : Parameter} (c : Cell m) : ℤ :=
  if c.r = 0 then
    if c.e = 1 ∧ c.v = 1 ∧ c.s < m.val - 1 then 1 else 0
  else if c.r = 1 then
    if c.e = 0 then
      if c.v = 0 then (if 0 < c.s then 1 else 0)
      else (if c.s = m.val - 1 then 1 else 0)
    else if c.v = 0 then 0 else 1
  else if c.s = m.val - 1 then
    if c.e = 0 then
      if c.v = 0 then 1 else 0
    else if c.v = 0 then 1 else (if c.r = 2 then 0 else 1)
  else if c.r = m.val + 1 ∧ c.s = m.val - 2 ∧ c.v = 1 then
    if c.e = 0 then 2 else 0
  else if c.e = 0 then
    if c.v = 0 then 1 - (if 1 ≤ c.r - c.s ∧ c.r - c.s ≤ 3 then 1 else 0)
    else (if c.r - c.s = 2 ∨ c.r - c.s = 3 then 1 else 0)
  else if c.v = 0 then (if c.r - c.s = 2 ∨ c.r - c.s = 3 then 1 else 0)
  else 1 - (if 2 ≤ c.r - c.s ∧ c.r - c.s ≤ 4 then 1 else 0)

/-- Off the prescribed cell the displayed table is binary. This assertion is
about the table; the identification with the actual deficit is proved separately. -/
theorem cellDeficitTable_zero_or_one {m : Parameter} (c : Cell m)
    (hNotPrescribed : ¬cellPrescribed c) :
    cellDeficitTable c = 0 ∨ cellDeficitTable c = 1 := by
  unfold cellPrescribed at hNotPrescribed
  unfold cellDeficitTable
  split_ifs <;> omega

end FLattice.Auxiliary.PlusOddProfile
