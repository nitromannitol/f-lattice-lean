import FLattice.Auxiliary.PlusOddPredecessors
import FLattice.Auxiliary.PlusOddDeficit
import Mathlib.Algebra.BigOperators.Fin

/-!
# Physical incoming sums for the odd comparison

The indexed sums and decoded incoming cells are identified with the actual
odd-native edges. Periodicity is used only for the reference deficit and
representative geometry, never for the compared unknown function.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The indexed sum is exactly the odd-native horizontal or vertical sum. -/
theorem incomingPoint_sum (h : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ i : Fin 2, h (incomingPoint x y i)) =
      if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
      else h (x, y - 1) + h (x, y + 1) := by
  simp only [Fin.sum_univ_two, incomingPoint]
  split_ifs <;> norm_num [sub_eq_add_neg] at *

/-- The actual deficit equals the residual in the capped incoming inequality. -/
theorem incomingDeficit_eq_residual (m : Parameter) (x y : ℤ) :
    incomingDeficit m x y =
      0 - ((∑ i : Fin 2, profile m (incomingPoint x y i).1 (incomingPoint x y i).2) -
        2 * profile m x y) := by
  rw [incomingPoint_sum (fun z => profile m z.1 z.2)]
  unfold incomingDeficit
  split_ifs <;> dsimp <;> ring

/-- The full signed lift preserves the literal deficit of the decoded cell. -/
theorem incomingDeficit_eq_cell (m : Parameter) (x y : ℤ) :
    incomingDeficit m x y =
      incomingDeficit m (cellOf m x y).x (cellOf m x y).y := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := incomingDeficit_add_periods m (cellOf m x y).x (cellOf m x y).y k q
  rw [add_comm (cellOf m x y).y (2 * k), ← hx, ← hy] at h
  exact h

/-- Taking a physical incoming step then decoding gives the representative input. -/
theorem cellOf_incomingPoint (m : Parameter) (x y : ℤ) (i : Fin 2) :
    cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2 =
      incomingCell (cellOf m x y) i := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := cellOf_incomingPoint_lifted_cell m (cellOf m x y) k q i
  rw [← hx, ← hy] at h
  exact h

end FLattice.Auxiliary.PlusOddProfile
