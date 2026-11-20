import FLattice.Auxiliary.MinusSmallDeficit
import Mathlib.Algebra.BigOperators.Fin

/-!
# The complete bounded clocks for smallest-minus comparison

The eight printed integer clocks are evaluated on actual signed physical
coordinates. Their strict selected-input inequality includes all sixteen
native stars and all period translates; the unknown function is not periodic.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.MinusSmallProfile

/-- Actual native incoming slots, retaining their order and multiplicity. -/
def incomingPoint (ε : Fin 2) (x y : ℤ) (i : Fin 2) : ℤ × ℤ :=
  if (x + y + (ε.val : ℤ)) % 2 = 0 then
    (x + (if i = 0 then -1 else 1), y)
  else (x, y + (if i = 0 then -1 else 1))

/-- The literal source clock, indexed by the eight representatives. -/
def representativeClock (ε : Fin 2) (X : Fin 4) (e : Fin 2) : ℤ :=
  if ε = 0 then
    if e = 0 then (if X = 0 ∨ X = 2 then 3 else 2)
    else if X = 0 then 0 else if X = 1 then 5 else if X = 2 then 4 else 1
  else if e = 0 then (if X = 0 ∨ X = 2 then 3 else if X = 1 then 4 else 0)
    else if X = 0 ∨ X = 2 then 2 else if X = 1 then 5 else 1

/-- The global clock uses the same signed Euclidean decoder as the profile. -/
def clock (ε : Fin 2) (x y : ℤ) : ℤ :=
  representativeClock ε (horizontalState (x - 2 * (y / 2))) (binaryState y)

/-- The bounded clock is nonnegative everywhere. -/
theorem clock_nonneg (ε : Fin 2) (x y : ℤ) : 0 ≤ clock ε x y := by
  unfold clock representativeClock
  split_ifs <;> omega

/-- All signed translations by the two periods preserve the clock. -/
theorem clock_add_periods (ε : Fin 2) (x y k q : ℤ) :
    clock ε (x + 2 * k + 4 * q) (y + 2 * k) = clock ε x y := by
  have hRow : (y + 2 * k) / 2 = y / 2 + k := by omega
  have hReduced : x + 2 * k + 4 * q - 2 * (y / 2 + k) =
      x - 2 * (y / 2) + 4 * q := by ring
  have hBinary : binaryState (y + 2 * k) = binaryState y := by
    apply Fin.ext
    have h₁ := binaryState_val (y + 2 * k)
    have h₂ := binaryState_val y
    omega
  have hHorizontal : horizontalState (x - 2 * (y / 2) + 4 * q) =
      horizontalState (x - 2 * (y / 2)) := by
    apply Fin.ext
    have h₁ := horizontalState_val (x - 2 * (y / 2) + 4 * q)
    have h₂ := horizontalState_val (x - 2 * (y / 2))
    omega
  simp only [clock, hRow, hReduced, hBinary, hHorizontal]

/-- The clock at each actual representative is exactly its printed value. -/
theorem clock_at_cell (ε : Fin 2) (X : Fin 4) (e : Fin 2) :
    clock ε (X.val : ℤ) (e.val : ℤ) = representativeClock ε X e := by
  have he := e.isLt
  have hRow : (e.val : ℤ) / 2 = 0 := by omega
  simp only [clock, hRow, mul_zero, sub_zero,
    horizontalState_of_coordinate, binaryState_of_bit]

/-- The actual incoming slots commute with every signed period translation. -/
theorem incomingPoint_add_periods (ε : Fin 2) (x y k q : ℤ) (i : Fin 2) :
    incomingPoint ε (x + 2 * k + 4 * q) (y + 2 * k) i =
      ((incomingPoint ε x y i).1 + 2 * k + 4 * q,
        (incomingPoint ε x y i).2 + 2 * k) := by
  unfold incomingPoint
  rw [period_lift_parity]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

/-- The number of strictly smaller incoming clocks exceeds the actual deficit
at every nonprescribed representative. This is the complete finite table check. -/
theorem representative_clock_count (ε : Fin 2) (X : Fin 4) (e : Fin 2)
    (hNotPin : ¬representativePrescribed ε X e) :
    representativeDeficit ε X e <
      ((Finset.univ.filter fun i : Fin 2 =>
        clock ε (incomingPoint ε (X.val : ℤ) (e.val : ℤ) i).1
          (incomingPoint ε (X.val : ℤ) (e.val : ℤ) i).2 <
            clock ε (X.val : ℤ) (e.val : ℤ)).card : ℤ) := by
  fin_cases ε <;> fin_cases X <;> fin_cases e <;>
    norm_num [representativePrescribed, Fin.ext_iff] at hNotPin
  all_goals decide

/-- On the whole integer plane, enough actual incoming slots strictly lower
the bounded clock. There is no quotient-periodicity assumption on the unknown. -/
theorem clock_selected (ε : Fin 2) (x y : ℤ)
    (hNotPin : ¬prescribedCoset ε x y) :
    ∃ S : Finset (Fin 2), incomingDeficit ε x y < (S.card : ℤ) ∧
      ∀ i ∈ S, clock ε (incomingPoint ε x y i).1 (incomingPoint ε x y i).2 <
        clock ε x y := by
  obtain ⟨X, e, k, q, rfl, rfl⟩ := exists_lifted_cell x y
  have hNotRep := mt (prescribedCoset_at_lifted_cell ε X e k q).mpr hNotPin
  let S := Finset.univ.filter fun i : Fin 2 =>
    clock ε (incomingPoint ε (X.val : ℤ) (e.val : ℤ) i).1
      (incomingPoint ε (X.val : ℤ) (e.val : ℤ) i).2 < clock ε (X.val : ℤ) (e.val : ℤ)
  refine ⟨S, ?_, ?_⟩
  · rw [incomingDeficit_at_lifted_cell]
    exact representative_clock_count ε X e hNotRep
  · intro i hi
    have hSmall := (Finset.mem_filter.mp hi).2
    rw [add_comm (2 * k) (e.val : ℤ), incomingPoint_add_periods]
    simp only [clock_add_periods]
    exact hSmall

/-- Indexed incoming sums are literally the native source stars. -/
theorem incomingPoint_sum (ε : Fin 2) (h : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ i : Fin 2, h (incomingPoint ε x y i)) =
      if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
      else h (x, y - 1) + h (x, y + 1) := by
  simp only [Fin.sum_univ_two, incomingPoint]
  split_ifs <;> norm_num [sub_eq_add_neg] at *

end FLattice.Auxiliary.MinusSmallProfile
