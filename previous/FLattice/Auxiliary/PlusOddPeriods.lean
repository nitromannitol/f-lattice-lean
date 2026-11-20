import FLattice.Auxiliary.PlusOddProfile
import FLattice.Auxiliary.PlusEvenPeriods

/-!
# The two affine periods of the odd-plus profile

Changing only the literal Euclidean reduction proves both identities on
all signed physical coordinates. The odd affine terms are retained; no
superharmonicity, recurrence or comparison assertion is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- Translation by `(2m, 2)` has affine increment `-y - 1`. -/
theorem profile_add_diagonal_period (m : Parameter) (x y : ℤ) :
    profile m (x + 2 * m.val) (y + 2) - profile m x y = -y - 1 := by
  have hk : (y + 2) / 2 = y / 2 + 1 := by omega
  have he : (y + 2) % 2 = y % 2 := by omega
  have hReduced : x + 2 * m.val - 2 * m.val * (y / 2 + 1) =
      x - 2 * m.val * (y / 2) := by ring
  simp only [profile, hk, he, binaryState_add_two, hReduced]
  ring_nf
  omega

/-- Translation by the full horizontal period `2J` has its exact affine
increment, for arbitrary signed coordinates and every allowed parameter. -/
theorem profile_add_horizontal_period (m : Parameter) (x y : ℤ) :
    profile m (x + 2 * halfPeriod m) y - profile m x y =
      -x + m.val * y - halfPeriod m + m.val - 1 := by
  have hPeriodNe : 2 * halfPeriod m ≠ 0 := by
    have hPositive := halfPeriod_pos m
    omega
  have hReduced : x + 2 * halfPeriod m - 2 * m.val * (y / 2) =
      (x - 2 * m.val * (y / 2)) + 2 * halfPeriod m := by ring
  have hQuotient :
      ((x - 2 * m.val * (y / 2)) + 2 * halfPeriod m) / (2 * halfPeriod m) =
        (x - 2 * m.val * (y / 2)) / (2 * halfPeriod m) + 1 := by
    simpa only [one_mul] using
      Int.add_mul_ediv_right (x - 2 * m.val * (y / 2)) 1 hPeriodNe
  have hRemainder :
      ((x - 2 * m.val * (y / 2)) + 2 * halfPeriod m) % (2 * halfPeriod m) =
        (x - 2 * m.val * (y / 2)) % (2 * halfPeriod m) :=
    Int.add_emod_right _ _
  have hReconstruct := Int.emod_add_mul_ediv
    (x - 2 * m.val * (y / 2)) (2 * halfPeriod m)
  have hy : y % 2 + 2 * (y / 2) = y := by omega
  have hScaledY := congrArg (fun t : ℤ => m.val * t) hy
  simp only [profile, hReduced, hQuotient, hRemainder]
  ring_nf at hReconstruct hScaledY ⊢
  omega

end FLattice.Auxiliary.PlusOddProfile
