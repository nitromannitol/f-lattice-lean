import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Integer hinge identities for the even-plus bulk profile

These are identities of explicit functions on all integers. They describe
only the uncorrected, unwrapped representative formulas; no statement about
period seams, exceptional heights, or the global F-lattice profile is made.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenBulk

/-- The literal `00` hinge of the even-plus bulk formula. -/
def h00 (a : ℤ) : ℤ :=
  2 * max (a - 1) 0 + if a = 1 ∨ a = 2 then 1 else 0

/-- The literal common `01` and `10` hinge. -/
def h01 (a : ℤ) : ℤ :=
  max (a - 1) 0 + max (a - 2) 0 + if a = 2 then 1 else 0

/-- The `10` hinge agrees exactly with the `01` hinge. -/
def h10 (a : ℤ) : ℤ := h01 a

/-- The literal `11` hinge of the even-plus bulk formula. -/
def h11 (a : ℤ) : ℤ :=
  2 * max (a - 2) 0 + if a = 2 ∨ a = 3 then 1 else 0

/-- The horizontal `00` deficit is supported at `a = 2`. -/
theorem h00_deficit (a : ℤ) :
    2 * h00 a - h01 (a + 1) - h01 a = if a = 2 then 1 else 0 := by
  unfold h00 h01
  omega

/-- The vertical `01` deficit vanishes exactly at `a = 1, 3`. -/
theorem h01_deficit (a : ℤ) :
    1 + 2 * h01 a - h11 (a + 1) - h11 a =
      if a = 1 ∨ a = 3 then 0 else 1 := by
  unfold h01 h11
  omega

/-- The vertical `10` deficit has the same two exceptional arguments. -/
theorem h10_deficit (a : ℤ) :
    1 + 2 * h01 a - h00 a - h00 (a - 1) =
      if a = 1 ∨ a = 3 then 0 else 1 := by
  unfold h01 h00
  omega

/-- The horizontal `11` deficit is supported at `a = 3`. -/
theorem h11_deficit (a : ℤ) :
    2 * h11 a - h01 a - h01 (a - 1) = if a = 3 then 1 else 0 := by
  unfold h11 h01
  omega

/-- Uncorrected `00` representative height, without low-row exceptions. -/
def u00 (r s : ℤ) : ℤ := -(r ^ 2) - 1 + h00 (r - s)

/-- Uncorrected `01` representative height. -/
def u01 (r s : ℤ) : ℤ := -(r ^ 2) - 1 + h01 (r - s)

/-- Uncorrected `10` representative height, without low-row exceptions. -/
def u10 (r s : ℤ) : ℤ := -(r ^ 2) + r - 2 + h10 (r - s)

/-- Uncorrected `11` representative height, without low-row exceptions. -/
def u11 (r s : ℤ) : ℤ := -(r ^ 2) + r - 2 + h11 (r - s)

/-- The unwrapped `00` star uses two horizontal representatives. -/
theorem u00_deficit (r s : ℤ) :
    2 * u00 r s - u01 r (s - 1) - u01 r s =
      if r - s = 2 then 1 else 0 := by
  calc
    2 * u00 r s - u01 r (s - 1) - u01 r s =
        2 * h00 (r - s) - h01 (r - s + 1) - h01 (r - s) := by
      unfold u00 u01
      rw [show r - (s - 1) = r - s + 1 by omega]
      ring
    _ = _ := h00_deficit (r - s)

/-- The unwrapped `01` downward input includes the affine correction `+1`. -/
theorem u01_deficit (r s : ℤ) :
    2 * u01 r s - (u11 (r + 1) s + 1) - u11 r s =
      if r - s = 1 ∨ r - s = 3 then 0 else 1 := by
  calc
    2 * u01 r s - (u11 (r + 1) s + 1) - u11 r s =
        1 + 2 * h01 (r - s) - h11 (r - s + 1) - h11 (r - s) := by
      unfold u01 u11
      rw [show r + 1 - s = r - s + 1 by omega]
      ring
    _ = _ := h01_deficit (r - s)

/-- The unwrapped `10` upward input includes the affine correction `-2`. -/
theorem u10_deficit (r s : ℤ) :
    2 * u10 r s - u00 r s - (u00 (r - 1) s - 2) =
      if r - s = 1 ∨ r - s = 3 then 0 else 1 := by
  calc
    2 * u10 r s - u00 r s - (u00 (r - 1) s - 2) =
        1 + 2 * h01 (r - s) - h00 (r - s) - h00 (r - s - 1) := by
      unfold u10 u00 h10
      rw [show r - 1 - s = r - s - 1 by omega]
      ring
    _ = _ := h10_deficit (r - s)

/-- The unwrapped `11` star uses two horizontal representatives. -/
theorem u11_deficit (r s : ℤ) :
    2 * u11 r s - u10 r s - u10 r (s + 1) =
      if r - s = 3 then 1 else 0 := by
  calc
    2 * u11 r s - u10 r s - u10 r (s + 1) =
        2 * h11 (r - s) - h01 (r - s) - h01 (r - s - 1) := by
      unfold u11 u10 h10
      rw [show r - (s + 1) = r - s - 1 by omega]
      ring
    _ = _ := h11_deficit (r - s)

end FLattice.Auxiliary.PlusEvenBulk
