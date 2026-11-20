import Mathlib.Data.Int.Order.Basic
import Lean.Elab.Tactic.Omega

/-!
# Literal directional ranks on integer lattice coordinates

The edge identities concern actual physical coordinates, including negative
ones. Only parity is assumed: no profile, region or selection policy appears.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.DirectionalRank

/-- The rank that decreases on a horizontal left incoming edge. -/
def leftRank (x y : ℤ) : ℤ := 2 * x + (x + y) % 2

/-- The rank that decreases on a horizontal right incoming edge. -/
def rightRank (x y : ℤ) : ℤ := -2 * x + (x + y) % 2

/-- At an even site, the physical left incoming edge lowers `leftRank` by one. -/
theorem leftRank_left_of_even (x y : ℤ) (hEven : (x + y) % 2 = 0) :
    leftRank (x - 1) y = leftRank x y - 1 := by
  unfold leftRank
  omega

/-- At an even site, the physical right incoming edge lowers `rightRank` by one. -/
theorem rightRank_right_of_even (x y : ℤ) (hEven : (x + y) % 2 = 0) :
    rightRank (x + 1) y = rightRank x y - 1 := by
  unfold rightRank
  omega

/-- At an odd site, both physical vertical incoming edges lower `leftRank` by one. -/
theorem leftRank_vertical_of_odd (x y : ℤ) (hOdd : (x + y) % 2 = 1) :
    leftRank x (y - 1) = leftRank x y - 1 ∧
      leftRank x (y + 1) = leftRank x y - 1 := by
  unfold leftRank
  omega

/-- At an odd site, both physical vertical incoming edges lower `rightRank` by one. -/
theorem rightRank_vertical_of_odd (x y : ℤ) (hOdd : (x + y) % 2 = 1) :
    rightRank x (y - 1) = rightRank x y - 1 ∧
      rightRank x (y + 1) = rightRank x y - 1 := by
  unfold rightRank
  omega

/-- Every even-parity translation changes `leftRank` by twice its horizontal displacement. -/
theorem leftRank_add_of_even (x y a b : ℤ) (hEven : (a + b) % 2 = 0) :
    leftRank (x + a) (y + b) = leftRank x y + 2 * a := by
  unfold leftRank
  omega

/-- Every even-parity translation changes `rightRank` by minus twice its horizontal displacement. -/
theorem rightRank_add_of_even (x y a b : ℤ) (hEven : (a + b) % 2 = 0) :
    rightRank (x + a) (y + b) = rightRank x y - 2 * a := by
  unfold rightRank
  omega

end FLattice.Auxiliary.DirectionalRank
