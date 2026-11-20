import FLattice.Auxiliary.PlusEvenProfile

/-!
# Affine periods of the literal even-plus profile

The two identities hold for every signed physical coordinate. They use the
corrected global profile, including both low-row overrides. The proof only
changes its Euclidean reduction coordinates; it does not assume any local
superharmonicity or periodicity theorem.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- Adding two preserves the signed integer's binary state. -/
theorem binaryState_add_two (y : ℤ) : binaryState (y + 2) = binaryState y := by
  apply Fin.ext
  simp only [binaryState, Int.add_emod_right]

/-- Translation by `(2m, 2)` has affine increment `-y - 2`. -/
theorem profile_add_diagonal_period (m : Parameter) (x y : ℤ) :
    profile m (x + 2 * m.val) (y + 2) - profile m x y = -y - 2 := by
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
      -x + m.val * y - halfPeriod m := by
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

/-- The diagonal period preserves physical parity. -/
theorem diagonal_period_parity (m : Parameter) (x y : ℤ) :
    (x + 2 * m.val + (y + 2)) % 2 = (x + y) % 2 := by
  omega

/-- The horizontal period preserves physical parity. -/
theorem horizontal_period_parity (m : Parameter) (x y : ℤ) :
    (x + 2 * halfPeriod m + y) % 2 = (x + y) % 2 := by
  omega

end FLattice.Auxiliary.PlusEvenProfile
