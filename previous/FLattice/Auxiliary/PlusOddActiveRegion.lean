import FLattice.Auxiliary.PlusOddCellData

/-!
# The smaller odd contact region as an actual subset of the plane

The displayed bands use representatives modulo the diagonal period only.
The physical region is their integer diagonal translates; no horizontal
period is allowed in its membership definition. The canonical decoder is
used to recover a witness, not to enlarge this region by another period.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The source's finite set of representative bands for the contact argument. -/
def cellActive {m : Parameter} (c : Cell m) : Prop :=
  if c.e = 0 then
    c.r = 0 ∨ (1 ≤ c.r ∧ c.r ≤ m.val - 1 ∧ c.r - 1 ≤ c.s ∧ c.s ≤ m.val - 2)
  else if c.v = 0 then
    c.r = 1 ∨ (2 ≤ c.r ∧ c.r ≤ m.val ∧ c.r - 1 ≤ c.s ∧ c.s ≤ m.val - 2)
  else
    (c.r = 0 ∧ c.s = m.val - 1) ∨ (c.r = 1 ∧ c.s ≤ m.val - 2) ∨
      (2 ≤ c.r ∧ c.r ≤ m.val ∧ c.r - 2 ≤ c.s ∧ c.s ≤ m.val - 2)

/-- The actual active region consists only of diagonal-period lifts of those bands. -/
def activePoint (m : Parameter) (x y : ℤ) : Prop :=
  ∃ c : Cell m, cellActive c ∧ ∃ k : ℤ,
    x = c.x + 2 * m.val * k ∧ y = 2 * k + c.y

/-- Active representative bands avoid the prescribed top cell. -/
theorem cellActive_not_prescribed {m : Parameter} (c : Cell m)
    (hActive : cellActive c) : ¬cellPrescribed c := by
  have hm := m.property
  have hRow : c.r ≤ m.val := by
    unfold cellActive at hActive
    split_ifs at hActive <;> omega
  intro hPin
  have hPinRow := hPin.1
  omega

/-- Decoding an active physical point recovers an active band representative. -/
theorem cellActive_cellOf_of_activePoint (m : Parameter) (x y : ℤ)
    (hActive : activePoint m x y) : cellActive (cellOf m x y) := by
  obtain ⟨c, hc, k, hx, hy⟩ := hActive
  have hDecode := cellOf_lifted_cell m c k 0
  simp only [mul_zero, add_zero] at hDecode
  rw [← hx, ← hy] at hDecode
  rw [hDecode]
  exact hc

/-- The origin lies in the source contact region for every allowed parameter. -/
theorem activePoint_origin (m : Parameter) : activePoint m 0 0 := by
  have hm := m.property
  let c : Cell m := ⟨0, 0, 0, 0,
    by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨c, ?_, 0, ?_, ?_⟩
  · simp [cellActive, c]
  · simp [Cell.x, c]
  · simp [Cell.y, c]

/-- No physical active point belongs to the prescribed cell class. -/
theorem activePoint_not_prescribed (m : Parameter) (x y : ℤ)
    (hActive : activePoint m x y) : ¬cellPrescribed (cellOf m x y) :=
  cellActive_not_prescribed (cellOf m x y)
    (cellActive_cellOf_of_activePoint m x y hActive)

end FLattice.Auxiliary.PlusOddProfile
