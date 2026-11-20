import FLattice.Auxiliary.MiddleProfile

/-!
# Exact signed reductions for the two middle profiles

Every physical integer point has the source's Euclidean representative.
The formulas below recover every valid representative at arbitrary signed
period indices, and the existence statement uses the literal decoder.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

/-- The two Euclidean quotients and residues reconstruct any signed point. -/
theorem canonical_reduction (x y : ℤ) :
    x = ((horizontalState (x - 2 * (y / 2))).val : ℤ) +
      2 * (y / 2) + 4 * ((x - 2 * (y / 2)) / 4) ∧
    y = 2 * (y / 2) + ((binaryState y).val : ℤ) := by
  rw [horizontalState_val, binaryState_val]
  omega

/-- The exact literal decoder covers every physical integer point. -/
theorem exists_lifted_cell (x y : ℤ) :
    ∃ X : Fin 4, ∃ e : Fin 2, ∃ k q : ℤ,
      x = (X.val : ℤ) + 2 * k + 4 * q ∧ y = 2 * k + (e.val : ℤ) := by
  refine ⟨horizontalState (x - 2 * (y / 2)), binaryState y,
    y / 2, (x - 2 * (y / 2)) / 4, ?_⟩
  exact canonical_reduction x y

/-- A prescribed Euclidean reduction gives exactly the source affine formula. -/
theorem profile_of_reduction (ε : Fin 2) (x y k q : ℤ) (X : Fin 4) (e : Fin 2)
    (hy : y = 2 * k + (e.val : ℤ))
    (hx : x - 2 * k = (X.val : ℤ) + 4 * q) :
    profile ε x y = representativeHeight ε X e - q * (X.val : ℤ) +
      q * (e.val : ℤ) - 2 * q ^ 2 - k * (e.val : ℤ) - k ^ 2 -
      (1 - (ε.val : ℤ)) * k := by
  have he := e.isLt
  have hX := X.isLt
  have hRow : y / 2 = k ∧ y % 2 = (e.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by omega, by omega, by omega⟩
  have hCol : (x - 2 * k) / 4 = q ∧ (x - 2 * k) % 4 = (X.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 4)).mpr
    exact ⟨by omega, by omega, by omega⟩
  have hBit : binaryState y = e := by
    apply Fin.ext
    have hValue := binaryState_val y
    omega
  have hCoordinate : horizontalState (x - 2 * k) = X := by
    apply Fin.ext
    have hValue := horizontalState_val (x - 2 * k)
    omega
  simp only [profile, hRow.1, hRow.2, hCol.1, hCol.2, hBit, hCoordinate]

/-- Every representative and every signed pair of period indices obeys the
literal affine extension; no growth or local-star premise is involved. -/
theorem profile_at_lifted_cell (ε : Fin 2) (X : Fin 4) (e : Fin 2) (k q : ℤ) :
    profile ε ((X.val : ℤ) + 2 * k + 4 * q) (2 * k + (e.val : ℤ)) =
      representativeHeight ε X e - q * (X.val : ℤ) + q * (e.val : ℤ) -
        2 * q ^ 2 - k * (e.val : ℤ) - k ^ 2 - (1 - (ε.val : ℤ)) * k := by
  exact profile_of_reduction ε _ _ k q X e rfl (by ring)

/-- The global function restricts to the literal table on its eight representatives. -/
theorem profile_at_cell (ε : Fin 2) (X : Fin 4) (e : Fin 2) :
    profile ε (X.val : ℤ) (e.val : ℤ) = representativeHeight ε X e := by
  simpa using profile_at_lifted_cell ε X e 0 0

end FLattice.Auxiliary.MiddleProfile
