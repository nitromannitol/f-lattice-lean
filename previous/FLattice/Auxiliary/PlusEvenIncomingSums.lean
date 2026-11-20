import FLattice.Auxiliary.PlusEvenPredecessors
import FLattice.Auxiliary.PlusEvenDeficitGlobal
import FLattice.Auxiliary.CappedStagedComparison
import Mathlib.Algebra.BigOperators.Fin

/-!
# Incoming sums and the representative deficit

These identities bridge the literal two incoming physical points, the
indexed sums in the generic comparison theorem, and the proved deficit.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.PlusEvenProfile

/-- An indexed incoming sum is the native parity-dependent two-point sum. -/
theorem incomingPoint_sum (h : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ i : Fin 2, h (incomingPoint x y i)) =
      if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
      else h (x, y - 1) + h (x, y + 1) := by
  simp only [Fin.sum_univ_two, incomingPoint]
  split_ifs <;> norm_num [sub_eq_add_neg] at *

/-- The literal physical deficit equals the residual used by capped comparison. -/
theorem incomingDeficit_eq_residual (m : Parameter) (x y : ℤ) :
    incomingDeficit m x y =
      0 - ((∑ i : Fin 2, profile m (incomingPoint x y i).1 (incomingPoint x y i).2) -
        2 * profile m x y) := by
  rw [incomingPoint_sum (fun z => profile m z.1 z.2)]
  unfold incomingDeficit
  split_ifs <;> dsimp <;> ring

/-- The full signed lift preserves the deficit of the decoded cell. -/
theorem incomingDeficit_eq_cell (m : Parameter) (x y : ℤ) :
    incomingDeficit m x y =
      incomingDeficit m (cellOf m x y).x (cellOf m x y).y := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := incomingDeficit_add_periods m (cellOf m x y).x (cellOf m x y).y k q
  rw [add_comm (cellOf m x y).y (2 * k), ← hx, ← hy] at h
  exact h

end FLattice.Auxiliary.PlusEvenProfile
