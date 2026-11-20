import FLattice.Auxiliary.PlusEvenCells
import Mathlib.Tactic.SplitIfs

/-!
# The literal odd-plus comparison clock

Two four-phase bulk paths meet at two maximum rules. On valid cells the
pin pair, two bottom rows and last-column ladder take precedence. These
definitions reproduce the source's assignments. The clock is bounded
below; no incoming-edge decrease is asserted by this module.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The two path clocks and their two joining values, before boundary overrides. -/
def bulkClock (m r s : ℤ) (e v : Fin 2) : ℤ :=
  let a := r - s
  if e = 0 then
    if v = 0 then
      if a ≤ 1 then 4 * s + 3
      else 4 * m - 4 * (s + if 3 ≤ a then 1 else 0) - 1
    else
      if a ≤ 1 then 4 * s + 4
      else if a = 2 then max (4 * m - 4 * s) (4 * s + 8)
      else 4 * m - 4 * (s + if 4 ≤ a then 1 else 0) - 4
  else
    if v = 0 then
      if a ≤ 1 then 4 * s + 2
      else if a = 2 then max (4 * m - 4 * s + 2) (4 * s + 6)
      else 4 * m - 4 * (s + if 4 ≤ a then 1 else 0) - 2
    else
      if a ≤ 2 then 4 * s + 5
      else 4 * m - 4 * (s + if 4 ≤ a then 1 else 0) - 3

/-- The source clock on every valid representative, including all overrides. -/
def cellClock {m : Parameter} (c : Cell m) : ℤ :=
  if c.r = m.val + 1 ∧ c.s = m.val - 2 ∧ c.v = 1 then
    if c.e = 0 then 0 else 1
  else if c.r = 0 then
    if c.e = 0 then
      if c.v = 0 then min (4 * c.s + 3) (4 * (m.val - c.s) - 1)
      else if c.s = m.val - 1 then 4
      else min (4 * c.s + 4) (4 * (m.val - c.s) - 4)
    else
      if c.v = 0 then
        if c.s = 0 then 2 else 4 * (m.val - c.s) - 2
      else 4 * (m.val - c.s) - 3
  else if c.r = 1 then
    if c.e = 0 then
      if c.v = 0 then 4 * c.s + 3 else 4 * c.s + 4
    else if c.v = 0 then 4 * c.s + 2 else 4 * c.s + 5
  else if c.s = m.val - 1 then
    if c.e = 0 then
      if c.v = 0 then 4 * m.val - 1 else 4 * m.val - 4
    else if c.v = 0 then 4 * m.val - 2 else 4 * m.val - 3
  else bulkClock m.val c.r c.s c.e c.v

/-- All bulk clock values in the ordinary columns are nonnegative. -/
theorem bulkClock_nonneg (m r s : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s ≤ m - 2) :
    0 ≤ bulkClock m r s e v := by
  dsimp only [bulkClock]
  split_ifs <;> omega

/-- The actual cell clock is bounded below on its complete public carrier. -/
theorem cellClock_nonneg {m : Parameter} (c : Cell m) : 0 ≤ cellClock c := by
  have hm := m.property
  have hs := c.hs0
  have hsm := c.hsm
  by_cases hLast : c.s = m.val - 1
  · unfold cellClock
    split_ifs <;> omega
  · have hBulk := bulkClock_nonneg m.val c.r c.s c.e c.v (c.hs0) (by omega)
    unfold cellClock
    split_ifs <;> omega

/-- Decoding any physical point gives a nonnegative clock, without restricting
the point's sign or assuming a finite set of points. -/
theorem cellClock_cellOf_nonneg (m : Parameter) (x y : ℤ) :
    0 ≤ cellClock (cellOf m x y) :=
  cellClock_nonneg (cellOf m x y)

end FLattice.Auxiliary.PlusOddProfile
