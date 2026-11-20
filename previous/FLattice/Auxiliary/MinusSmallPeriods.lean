import FLattice.Auxiliary.MinusSmallProfile

/-!
# The actual affine periods of the two smallest-minus profiles

The identities follow from signed Euclidean division in the literal function.
All translations preserve the native parity parameter. No deficit, comparison,
recurrence or transport conclusion is assumed or proved here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

/-- Adding two preserves the binary decoder. -/
theorem binaryState_add_two (y : ℤ) : binaryState (y + 2) = binaryState y := by
  apply Fin.ext
  simp only [binaryState, Int.add_emod_right]

/-- Adding four preserves the horizontal decoder. -/
theorem horizontalState_add_four (x : ℤ) :
    horizontalState (x + 4) = horizontalState x := by
  apply Fin.ext
  simp only [horizontalState, Int.add_emod_right]

/-- The diagonal period has the exact parity-dependent affine increment. -/
theorem profile_add_diagonal_period (ε : Fin 2) (x y : ℤ) :
    profile ε (x + 2) (y + 2) - profile ε x y = -y - 1 - (ε.val : ℤ) := by
  have hk : (y + 2) / 2 = y / 2 + 1 := by omega
  have he : (y + 2) % 2 = y % 2 := by omega
  have hReduced : x + 2 - 2 * (y / 2 + 1) = x - 2 * (y / 2) := by ring
  simp only [profile, hk, he, binaryState_add_two, hReduced]
  ring_nf
  omega

/-- The horizontal period has its exact affine increment on every signed point. -/
theorem profile_add_horizontal_period (ε : Fin 2) (x y : ℤ) :
    profile ε (x + 4) y - profile ε x y = -x + y - 2 + periodConstant ε := by
  have hReduced : x + 4 - 2 * (y / 2) = (x - 2 * (y / 2)) + 4 := by ring
  have hQuotient : ((x - 2 * (y / 2)) + 4) / 4 =
      (x - 2 * (y / 2)) / 4 + 1 := by omega
  have hRemainder : ((x - 2 * (y / 2)) + 4) % 4 =
      (x - 2 * (y / 2)) % 4 := by omega
  have hReconstruct := Int.emod_add_mul_ediv (x - 2 * (y / 2)) 4
  have hy : y % 2 + 2 * (y / 2) = y := by omega
  simp only [profile, hReduced, hQuotient, hRemainder, horizontalState_add_four]
  ring_nf
  omega

/-- The diagonal period preserves the actual native parity for either parameter. -/
theorem diagonal_period_parity (ε : Fin 2) (x y : ℤ) :
    (x + 2 + (y + 2) + (ε.val : ℤ)) % 2 = (x + y + (ε.val : ℤ)) % 2 := by
  omega

/-- The horizontal period preserves the actual native parity for either parameter. -/
theorem horizontal_period_parity (ε : Fin 2) (x y : ℤ) :
    (x + 4 + y + (ε.val : ℤ)) % 2 = (x + y + (ε.val : ℤ)) % 2 := by
  omega

/-- Every signed integer combination of the periods preserves native parity. -/
theorem period_lift_parity (ε : Fin 2) (x y k q : ℤ) :
    (x + 2 * k + 4 * q + (y + 2 * k) + (ε.val : ℤ)) % 2 =
      (x + y + (ε.val : ℤ)) % 2 := by
  omega

end FLattice.Auxiliary.MinusSmallProfile
