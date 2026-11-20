import FLattice.Auxiliary.MiddleProfile
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# The two physical minimum ranks for the smallest plus coefficient

These ranks are unbounded on the whole plane. They are used only on finite
minimum sets. At every vertex one actual incoming rank decreases; at even
coordinate-sum vertices both do, for either native parity convention.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.MiddleProfile

/-- The two actual incoming slots for the parity-shifted native graph. -/
def incomingPoint (ε : Fin 2) (x y : ℤ) (i : Fin 2) : ℤ × ℤ :=
  if (x + y + (ε.val : ℤ)) % 2 = 0 then
    (x + (if i = 0 then -1 else 1), y)
  else (x, y + (if i = 0 then -1 else 1))

/-- The literal physical rank in each of the source's two parity comparisons. -/
def physicalRank (ε : Fin 2) (x y : ℤ) : ℤ :=
  if ε = 0 then -2 * y - (x + y) % 2 else 2 * x + (x + y + 1) % 2

/-- Indexed incoming sums are exactly the source's native star sums. -/
theorem incomingPoint_sum (ε : Fin 2) (h : ℤ × ℤ → ℤ) (x y : ℤ) :
    (∑ i : Fin 2, h (incomingPoint ε x y i)) =
      if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
      else h (x, y - 1) + h (x, y + 1) := by
  simp only [Fin.sum_univ_two, incomingPoint]
  split_ifs <;> norm_num [sub_eq_add_neg] at *

/-- One incoming rank always decreases; both decrease at every even
coordinate-sum point, which includes every deficit-one class. -/
theorem physicalRank_decreasing_inputs (ε : Fin 2) (x y : ℤ) :
    (∃ i : Fin 2, physicalRank ε (incomingPoint ε x y i).1
      (incomingPoint ε x y i).2 < physicalRank ε x y) ∧
    ((x + y) % 2 = 0 → ∀ i : Fin 2,
      physicalRank ε (incomingPoint ε x y i).1 (incomingPoint ε x y i).2 <
        physicalRank ε x y) := by
  fin_cases ε
  · by_cases hp : (x + y) % 2 = 0
    · constructor
      · refine ⟨0, ?_⟩
        norm_num [incomingPoint, physicalRank, hp]
        omega
      · intro _ i
        fin_cases i <;> norm_num [incomingPoint, physicalRank, hp] <;> omega
    · constructor
      · refine ⟨1, ?_⟩
        norm_num [incomingPoint, physicalRank, hp]
        omega
      · intro hEven
        exact (hp hEven).elim
  · by_cases hp : (x + y) % 2 = 0
    · have hNative : (x + y + 1) % 2 ≠ 0 := by omega
      constructor
      · refine ⟨0, ?_⟩
        norm_num [incomingPoint, physicalRank, hNative]
        omega
      · intro _ i
        fin_cases i <;> norm_num [incomingPoint, physicalRank, hNative] <;> omega
    · have hNative : (x + y + 1) % 2 = 0 := by omega
      constructor
      · refine ⟨0, ?_⟩
        norm_num [incomingPoint, physicalRank, hNative]
        omega
      · intro hEven
        exact (hp hEven).elim

end FLattice.Auxiliary.MiddleProfile
