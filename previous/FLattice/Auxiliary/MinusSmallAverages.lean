import FLattice.Auxiliary.MinusZeroAverages

/-!
# The ten additional averages for the smallest minus coefficient

The two exceptional even thresholds use three and five native averages;
the exceptional odd threshold uses two. All input bounds remain explicit
here. The smallest comparison profiles must supply them in the eventual
transport proof; no profile or threshold implication is assumed proved.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

/-- The four bounds supplied at the smallest even threshold minus two. -/
theorem one_le_origin_of_small_even_minus_two_bounds
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLeft : 1 ≤ h (-1, 0)) (hUp : 0 ≤ h (0, 1))
    (hLowerRight : -1 ≤ h (1, -1)) (hUpperRight : -1 ≤ h (2, 1)) :
    1 ≤ h (0, 0) := by
  have hCorner : 0 ≤ h (1, 1) := by
    have hStar := hSuperharmonic 1 1
    norm_num at hStar
    omega
  have hRight : 0 ≤ h (1, 0) := by
    have hStar := hSuperharmonic 1 0
    norm_num at hStar
    omega
  have hStar := hSuperharmonic 0 0
  norm_num at hStar
  omega

/-- The five bounds supplied at the smallest even threshold minus one. -/
theorem one_le_origin_of_small_even_minus_one_bounds
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLowerLeft : 1 ≤ h (-2, -1)) (hUpperLeft : 0 ≤ h (-1, 1))
    (hDown : 0 ≤ h (0, -1)) (hUpperRight : -1 ≤ h (1, 1))
    (hLowerRight : -1 ≤ h (2, -1)) :
    1 ≤ h (0, 0) := by
  have hLeftCorner : 1 ≤ h (-1, -1) := by
    have hStar := hSuperharmonic (-1) (-1)
    norm_num at hStar
    omega
  have hLeft : 1 ≤ h (-1, 0) := by
    have hStar := hSuperharmonic (-1) 0
    norm_num at hStar
    omega
  have hRightCorner : 0 ≤ h (1, -1) := by
    have hStar := hSuperharmonic 1 (-1)
    norm_num at hStar
    omega
  have hRight : 0 ≤ h (1, 0) := by
    have hStar := hSuperharmonic 1 0
    norm_num at hStar
    omega
  have hStar := hSuperharmonic 0 0
  norm_num at hStar
  omega

/-- The three bounds supplied at the smallest odd threshold one. -/
theorem one_le_origin_of_small_odd_one_bounds
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLowerLeft : 1 ≤ h (-1, -1)) (hUp : 0 ≤ h (0, 1))
    (hLowerRight : 0 ≤ h (1, -1)) :
    1 ≤ h (0, 0) := by
  have hDown : 1 ≤ h (0, -1) := by
    have hStar := hSuperharmonic 0 (-1)
    norm_num at hStar
    omega
  have hStar := hSuperharmonic 0 0
  norm_num at hStar
  omega

end FLattice.Auxiliary.MinusProfile
