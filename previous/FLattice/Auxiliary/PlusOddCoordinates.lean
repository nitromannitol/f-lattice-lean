import FLattice.Auxiliary.PlusOddProfile
import FLattice.Auxiliary.PlusEvenCoordinates

/-!
# Exact signed coordinates for the odd-plus profile

The Euclidean geometry is shared with the even-plus period lattice, while
all heights and affine corrections refer to the independent odd profile.
The lift identity uses every signed pair of period indices and every valid
representative, including both low rows and the truncated last row.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- Decoding a cell in the strip recovers both indices and its binary state. -/
theorem stripHeight_at_cell (m : Parameter) (r s : ℤ) (e v : Fin 2)
    (hs0 : 0 ≤ s) (hsm : s < m.val) :
    stripHeight m (2 * m.val * r + 2 * s + (v.val : ℤ)) e =
      representativeHeight m e v r s := by
  have hm := parameter_pos m
  have hv := v.isLt
  have hFirst :
      (2 * m.val * r + 2 * s + (v.val : ℤ)) / (2 * m.val) = r ∧
      (2 * m.val * r + 2 * s + (v.val : ℤ)) % (2 * m.val) =
        2 * s + (v.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : 0 < 2 * m.val)).mpr
    exact ⟨by ring, by omega, by omega⟩
  have hSecond : (2 * s + (v.val : ℤ)) / 2 = s ∧
      (2 * s + (v.val : ℤ)) % 2 = (v.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by ring, by omega, by omega⟩
  have hBit : binaryState (2 * s + (v.val : ℤ)) = v := by
    apply Fin.ext
    have hValue := binaryState_val (2 * s + (v.val : ℤ))
    omega
  simp only [stripHeight, hFirst.1, hFirst.2, hSecond.1, hBit]

/-- The outer Euclidean reduction is exactly the displayed affine formula. -/
theorem profile_of_reduction (m : Parameter) (x y k q X : ℤ) (e : Fin 2)
    (hy : y = 2 * k + (e.val : ℤ))
    (hx : x - 2 * m.val * k = X + 2 * halfPeriod m * q)
    (hX0 : 0 ≤ X) (hXlt : X < 2 * halfPeriod m) :
    profile m x y = stripHeight m X e - q * X + q * m.val * (e.val : ℤ)
      - halfPeriod m * q ^ 2 + (m.val - 1) * q - k * (e.val : ℤ) - k ^ 2 := by
  have he := e.isLt
  have hRow : y / 2 = k ∧ y % 2 = (e.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by omega, by omega, by omega⟩
  have hCol : (x - 2 * m.val * k) / (2 * halfPeriod m) = q ∧
      (x - 2 * m.val * k) % (2 * halfPeriod m) = X := by
    apply (Int.ediv_emod_unique (by have := halfPeriod_pos m; omega)).mpr
    exact ⟨by omega, hX0, hXlt⟩
  have hBit : binaryState y = e := by
    apply Fin.ext
    have hValue := binaryState_val y
    omega
  simp only [profile, hRow.1, hRow.2, hCol.1, hCol.2, hBit]

/-- The affine extension agrees with the literal global function at every
valid representative and every signed pair of translation indices. -/
theorem profile_at_lifted_cell (m : Parameter) (r s k q : ℤ) (e v : Fin 2)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    profile m (2 * m.val * r + 2 * s + (v.val : ℤ) +
        2 * m.val * k + 2 * halfPeriod m * q) (2 * k + (e.val : ℤ)) =
      representativeHeight m e v r s - q * (2 * m.val * r + 2 * s + (v.val : ℤ))
        + q * m.val * (e.val : ℤ) - halfPeriod m * q ^ 2
        + (m.val - 1) * q - k * (e.val : ℤ) - k ^ 2 := by
  obtain ⟨hX0, hXlt⟩ := PlusEvenProfile.cell_coordinate_bounds m r s v hr0 hrm hs0 hsm hMissing
  rw [profile_of_reduction m _ _ k q
    (2 * m.val * r + 2 * s + (v.val : ℤ)) e rfl (by ring) hX0 hXlt]
  rw [stripHeight_at_cell m r s e v hs0 hsm]

end FLattice.Auxiliary.PlusOddProfile
