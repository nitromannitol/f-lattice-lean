import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The fixed integer averaging contradiction at minus threshold zero

These are the two seven-step chains and their final two averages from the
source. Every center uses its actual native F-lattice incoming pair. The
fourteen initial inequalities are explicit assumptions here; their
comparison-profile origin is proved separately.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

/-- Fourteen fixed lower bounds and a nonnegative origin force the origin
to be at least one, using only native integer superharmonicity. -/
theorem one_le_origin_of_fourteen_bounds
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hOrigin : 0 ≤ h (0, 0))
    (h0 : 0 ≤ h (-4, -3)) (h1 : -1 ≤ h (-2, -3))
    (h2 : 1 ≤ h (-3, -1)) (h3 : -2 ≤ h (0, -3))
    (h4 : 0 ≤ h (-1, -1)) (h5 : 0 ≤ h (-2, 0))
    (h6 : 0 ≤ h (0, -1)) (h7 : -1 ≤ h (-2, 1))
    (h8 : -1 ≤ h (-1, 1)) (h9 : -5 ≤ h (-2, 3))
    (h10 : -4 ≤ h (0, 3)) (h11 : 0 ≤ h (1, 1))
    (h12 : -3 ≤ h (2, 3)) (h13 : 0 ≤ h (1, 0)) :
    1 ≤ h (0, 0) := by
  have hLower0 : 0 ≤ h (-3, -3) := by
    have hStar := hSuperharmonic (-3) (-3)
    norm_num at hStar
    omega
  have hLower1 : 1 ≤ h (-3, -2) := by
    have hStar := hSuperharmonic (-3) (-2)
    norm_num at hStar
    omega
  have hLower2 : -1 ≤ h (-1, -3) := by
    have hStar := hSuperharmonic (-1) (-3)
    norm_num at hStar
    omega
  have hLower3 : 0 ≤ h (-1, -2) := by
    have hStar := hSuperharmonic (-1) (-2)
    norm_num at hStar
    omega
  have hLower4 : 1 ≤ h (-2, -2) := by
    have hStar := hSuperharmonic (-2) (-2)
    norm_num at hStar
    omega
  have hLower5 : 1 ≤ h (-2, -1) := by
    have hStar := hSuperharmonic (-2) (-1)
    norm_num at hStar
    omega
  have hLower6 : 1 ≤ h (-1, -1) := by
    have hStar := hSuperharmonic (-1) (-1)
    norm_num at hStar
    omega
  have hUpper0 : -4 ≤ h (-1, 3) := by
    have hStar := hSuperharmonic (-1) 3
    norm_num at hStar
    omega
  have hUpper1 : -2 ≤ h (-1, 2) := by
    have hStar := hSuperharmonic (-1) 2
    norm_num at hStar
    omega
  have hUpper2 : -3 ≤ h (1, 3) := by
    have hStar := hSuperharmonic 1 3
    norm_num at hStar
    omega
  have hUpper3 : -1 ≤ h (1, 2) := by
    have hStar := hSuperharmonic 1 2
    norm_num at hStar
    omega
  have hUpper4 : -1 ≤ h (0, 2) := by
    have hStar := hSuperharmonic 0 2
    norm_num at hStar
    omega
  have hUpper5 : 0 ≤ h (0, 1) := by
    have hStar := hSuperharmonic 0 1
    norm_num at hStar
    omega
  have hUpper6 : 0 ≤ h (-1, 1) := by
    have hStar := hSuperharmonic (-1) 1
    norm_num at hStar
    omega
  have hJoined : 1 ≤ h (-1, 0) := by
    have hStar := hSuperharmonic (-1) 0
    norm_num at hStar
    omega
  have hStar := hSuperharmonic 0 0
  norm_num at hStar
  omega

end FLattice.Auxiliary.MinusProfile
