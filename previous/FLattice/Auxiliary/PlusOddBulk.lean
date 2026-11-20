import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Ramp identities for the odd-plus bulk profile

The four functions below are the literal unmodified representative formulas
on arbitrary signed integer coordinates. The identities describe their
unwrapped stars only: low-row overrides, last-column corrections, and
period seams of the global comparison profile are separate assertions.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddBulk

/-- The unmodified `00` representative height. -/
def v00 (r s : ℤ) : ℤ :=
  -(r ^ 2) + r + max (r - s - 1) 0 + max (r - s - 3) 0

/-- The unmodified `01` representative height. -/
def v01 (r s : ℤ) : ℤ :=
  -(r ^ 2) + r + max (r - s - 1) 0 + max (r - s - 4) 0

/-- The unmodified `10` representative height. -/
def v10 (r s : ℤ) : ℤ :=
  -(r ^ 2) + 2 * r - 1 + max (r - s - 1) 0 + max (r - s - 4) 0

/-- The unmodified `11` representative height. -/
def v11 (r s : ℤ) : ℤ :=
  -(r ^ 2) + 2 * r - 1 + max (r - s - 2) 0 + max (r - s - 4) 0

/-- The `00` vertical star has no affine correction at its downward input. -/
theorem v00_deficit (r s : ℤ) :
    2 * v00 r s - v10 (r + 1) s - v10 r s =
      1 - (if 1 ≤ r - s ∧ r - s ≤ 3 then 1 else 0) := by
  unfold v00 v10
  ring_nf
  omega

/-- The `01` horizontal star has two adjacent `00` inputs. -/
theorem v01_deficit (r s : ℤ) :
    2 * v01 r s - v00 r s - v00 r (s + 1) =
      if r - s = 2 ∨ r - s = 3 then 1 else 0 := by
  unfold v01 v00
  ring_nf
  omega

/-- The `10` horizontal star has two adjacent `11` inputs. -/
theorem v10_deficit (r s : ℤ) :
    2 * v10 r s - v11 r (s - 1) - v11 r s =
      if r - s = 2 ∨ r - s = 3 then 1 else 0 := by
  unfold v10 v11
  ring_nf
  omega

/-- The `11` upward input has the literal affine correction `-1`. -/
theorem v11_deficit (r s : ℤ) :
    2 * v11 r s - v01 r s - (v01 (r - 1) s - 1) =
      1 - (if 2 ≤ r - s ∧ r - s ≤ 4 then 1 else 0) := by
  unfold v11 v01
  ring_nf
  omega

/-- The source's maximum equals the sum of its two ramps for every allowed phase.
Integer division gives the displayed floor and ceiling of the phase divided by two. -/
theorem max_eq_two_ramps (a b : ℤ) (hb0 : 0 ≤ b) (hb2 : b ≤ 2) :
    max (max 0 (2 * a - 4 - b)) (a - 1 - b / 2) =
      max (a - 1 - b / 2) 0 + max (a - 3 - (b + 1) / 2) 0 := by
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    norm_num only [Int.reduceAdd, Int.reduceDiv] <;> omega

end FLattice.Auxiliary.PlusOddBulk
