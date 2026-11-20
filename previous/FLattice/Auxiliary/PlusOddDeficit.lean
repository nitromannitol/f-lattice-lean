import FLattice.Auxiliary.PlusOddPeriods
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Periodic

/-!
# Periodicity of the literal odd-plus incoming deficit

The actual corrected global profile is evaluated on the odd native graph:
incoming neighbors are horizontal exactly when `(x+y+1) mod 2 = 0`.
Primitive affine increments give deficit invariance under every signed
combination of the period vectors. No deficit bound is asserted.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- Twice the odd profile value minus its two actual odd-native incoming values. -/
def incomingDeficit (m : Parameter) (x y : ℤ) : ℤ :=
  if (x + y + 1) % 2 = 0 then
    2 * profile m x y - profile m (x - 1) y - profile m (x + 1) y
  else
    2 * profile m x y - profile m x (y - 1) - profile m x (y + 1)

/-- The diagonal affine period leaves the odd-native deficit unchanged. -/
theorem incomingDeficit_add_diagonal_period (m : Parameter) (x y : ℤ) :
    incomingDeficit m (x + 2 * m.val) (y + 2) = incomingDeficit m x y := by
  have hParity : (x + 2 * m.val + (y + 2) + 1) % 2 = (x + y + 1) % 2 := by omega
  unfold incomingDeficit
  rw [hParity]
  have hCenter := profile_add_diagonal_period m x y
  split_ifs
  · have hLeft := profile_add_diagonal_period m (x - 1) y
    have hRight := profile_add_diagonal_period m (x + 1) y
    rw [show x + 2 * m.val - 1 = (x - 1) + 2 * m.val by ring,
      show x + 2 * m.val + 1 = (x + 1) + 2 * m.val by ring]
    omega
  · have hDown := profile_add_diagonal_period m x (y - 1)
    have hUp := profile_add_diagonal_period m x (y + 1)
    rw [show y + 2 - 1 = (y - 1) + 2 by omega,
      show y + 2 + 1 = (y + 1) + 2 by omega]
    omega

/-- The horizontal affine period leaves the odd-native deficit unchanged. -/
theorem incomingDeficit_add_horizontal_period (m : Parameter) (x y : ℤ) :
    incomingDeficit m (x + 2 * halfPeriod m) y = incomingDeficit m x y := by
  have hParity : (x + 2 * halfPeriod m + y + 1) % 2 = (x + y + 1) % 2 := by omega
  unfold incomingDeficit
  rw [hParity]
  have hCenter := profile_add_horizontal_period m x y
  split_ifs
  · have hLeft := profile_add_horizontal_period m (x - 1) y
    have hRight := profile_add_horizontal_period m (x + 1) y
    rw [show x + 2 * halfPeriod m - 1 = (x - 1) + 2 * halfPeriod m by ring,
      show x + 2 * halfPeriod m + 1 = (x + 1) + 2 * halfPeriod m by ring]
    omega
  · have hDown := profile_add_horizontal_period m x (y - 1)
    have hUp := profile_add_horizontal_period m x (y + 1)
    simp only [mul_sub, mul_add, mul_one] at hDown hUp
    omega

/-- Every signed combination of the two primitive periods preserves the deficit. -/
theorem incomingDeficit_add_periods (m : Parameter) (x y k q : ℤ) :
    incomingDeficit m (x + 2 * m.val * k + 2 * halfPeriod m * q) (y + 2 * k) =
      incomingDeficit m x y := by
  have hDiagonal : Function.Periodic
      (fun z : ℤ × ℤ => incomingDeficit m z.1 z.2) (2 * m.val, 2) := by
    intro z
    exact incomingDeficit_add_diagonal_period m z.1 z.2
  have hHorizontal : Function.Periodic
      (fun z : ℤ × ℤ => incomingDeficit m z.1 z.2) (2 * halfPeriod m, 0) := by
    intro z
    change incomingDeficit m (z.1 + 2 * halfPeriod m) (z.2 + 0) =
      incomingDeficit m z.1 z.2
    simpa only [add_zero] using incomingDeficit_add_horizontal_period m z.1 z.2
  have h := ((hDiagonal.zsmul k).add_period (hHorizontal.zsmul q)) (x, y)
  change incomingDeficit m
      (x + (k • (2 * m.val) + q • (2 * halfPeriod m)))
      (y + (k • (2 : ℤ) + q • (0 : ℤ))) = incomingDeficit m x y at h
  simp only [zsmul_eq_mul, Int.cast_id, mul_zero, add_zero] at h
  ring_nf at h ⊢
  exact h

end FLattice.Auxiliary.PlusOddProfile
