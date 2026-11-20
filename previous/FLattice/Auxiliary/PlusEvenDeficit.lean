import FLattice.Auxiliary.PlusEvenPeriods

/-!
# Periodicity of the literal even-plus incoming deficit

This is the actual deficit of the corrected global profile, with the native
incoming axis selected by physical parity. Its period invariance follows
from the affine increments and does not assert any deficit bound or global
superharmonicity.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- Twice the profile value minus the two native incoming values. -/
def incomingDeficit (m : Parameter) (x y : ℤ) : ℤ :=
  if (x + y) % 2 = 0 then
    2 * profile m x y - profile m (x - 1) y - profile m (x + 1) y
  else
    2 * profile m x y - profile m x (y - 1) - profile m x (y + 1)

/-- The diagonal affine period leaves the native incoming deficit unchanged. -/
theorem incomingDeficit_add_diagonal_period (m : Parameter) (x y : ℤ) :
    incomingDeficit m (x + 2 * m.val) (y + 2) = incomingDeficit m x y := by
  unfold incomingDeficit
  rw [diagonal_period_parity]
  have hCenter := profile_add_diagonal_period m x y
  split_ifs with hParity
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

/-- The horizontal affine period leaves the native incoming deficit unchanged. -/
theorem incomingDeficit_add_horizontal_period (m : Parameter) (x y : ℤ) :
    incomingDeficit m (x + 2 * halfPeriod m) y = incomingDeficit m x y := by
  unfold incomingDeficit
  rw [horizontal_period_parity]
  have hCenter := profile_add_horizontal_period m x y
  split_ifs with hParity
  · have hLeft := profile_add_horizontal_period m (x - 1) y
    have hRight := profile_add_horizontal_period m (x + 1) y
    rw [show x + 2 * halfPeriod m - 1 = (x - 1) + 2 * halfPeriod m by ring,
      show x + 2 * halfPeriod m + 1 = (x + 1) + 2 * halfPeriod m by ring]
    omega
  · have hDown := profile_add_horizontal_period m x (y - 1)
    have hUp := profile_add_horizontal_period m x (y + 1)
    simp only [mul_sub, mul_add, mul_one] at hDown hUp
    omega

end FLattice.Auxiliary.PlusEvenProfile
