import FLattice.Auxiliary.MinusProfile

/-!
# Affine periods of the general-minus profiles

Both identities use the literal canonical Cell and signed Euclidean indices.
The profile parity `ε` has the minus-family sign in the diagonal increment;
the vertical representative residue is a separate coordinate. All statements
hold on the full integer plane without local-star assumptions.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- The diagonal period W=(2m,2) has increment -y-1-ε. -/
theorem profile_add_diagonal_period (m : Parameter) (ε : Fin 2) (x y : ℤ) :
    profile m ε (x + 2 * m.val) (y + 2) - profile m ε x y =
      -y - 1 - (ε.val : ℤ) := by
  have hCell : cellOf m (x + 2 * m.val) (y + 2) = cellOf m x y := by
    simpa using cellOf_add_periods m x y 1 0
  have ht : (y + 2) / 2 = y / 2 + 1 := by omega
  have hReduced : x + 2 * m.val - 2 * m.val * (y / 2 + 1) =
      x - 2 * m.val * (y / 2) := by ring
  have hY : y = 2 * (y / 2) + (cellOf m x y).y := (canonical_lift m x y).2
  simp only [profile, hCell, ht, hReduced]
  ring_nf
  omega

/-- The full horizontal period has the exact parity-dependent constant cε. -/
theorem profile_add_horizontal_period (m : Parameter) (ε : Fin 2) (x y : ℤ) :
    profile m ε (x + 2 * halfPeriod m) y - profile m ε x y =
      -x + m.val * y - halfPeriod m + periodConstant m ε := by
  have hCell : cellOf m (x + 2 * halfPeriod m) y = cellOf m x y := by
    simpa using cellOf_add_periods m x y 0 1
  have hPeriodNe : 2 * halfPeriod m ≠ 0 := by
    have hPositive := halfPeriod_pos m
    omega
  have hReduced : x + 2 * halfPeriod m - 2 * m.val * (y / 2) =
      (x - 2 * m.val * (y / 2)) + 2 * halfPeriod m := by ring
  have hQuotient : ((x - 2 * m.val * (y / 2)) + 2 * halfPeriod m) /
      (2 * halfPeriod m) = (x - 2 * m.val * (y / 2)) / (2 * halfPeriod m) + 1 := by
    simpa only [one_mul] using
      Int.add_mul_ediv_right (x - 2 * m.val * (y / 2)) 1 hPeriodNe
  have hX : x = (cellOf m x y).x + 2 * m.val * (y / 2) +
      2 * halfPeriod m * ((x - 2 * m.val * (y / 2)) / (2 * halfPeriod m)) :=
    (canonical_lift m x y).1
  have hY : y = 2 * (y / 2) + (cellOf m x y).y := (canonical_lift m x y).2
  have hScaledY := congrArg (fun t : ℤ => m.val * t) hY
  simp only [profile, hCell, hReduced, hQuotient]
  ring_nf at hX hScaledY ⊢
  omega

/-- The diagonal period preserves the actual native parity. -/
theorem diagonal_period_parity (m : Parameter) (ε : Fin 2) (x y : ℤ) :
    (x + 2 * m.val + (y + 2) + (ε.val : ℤ)) % 2 =
      (x + y + (ε.val : ℤ)) % 2 := by
  omega

/-- The horizontal period preserves the actual native parity. -/
theorem horizontal_period_parity (m : Parameter) (ε : Fin 2) (x y : ℤ) :
    (x + 2 * halfPeriod m + y + (ε.val : ℤ)) % 2 =
      (x + y + (ε.val : ℤ)) % 2 := by
  omega

end FLattice.Auxiliary.MinusProfile
