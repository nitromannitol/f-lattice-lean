import FLattice.Auxiliary.MinusProfile

/-!
# Signed lifted-cell formulas for the general-minus profiles

The global decoder is the existing exact Cell decoder. Every signed lift of
a valid cell recovers its actual representative before the source affine
height correction is evaluated. No local-star or growth premise is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- A valid signed representative reduction gives precisely the source formula. -/
theorem profile_of_reduction (m : Parameter) (ε : Fin 2) (x y : ℤ)
    (c : Cell m) (t q : ℤ)
    (hy : y = 2 * t + c.y)
    (hx : x - 2 * m.val * t = c.x + 2 * halfPeriod m * q) :
    profile m ε x y = representativeHeight m ε c - q * c.x + q * m.val * c.y -
      halfPeriod m * q ^ 2 + periodConstant m ε * q - t * c.y - t ^ 2 -
      (ε.val : ℤ) * t := by
  have he := c.e.isLt
  obtain ⟨hX0, hXlt⟩ := cell_coordinate_bounds m c.r c.s c.v
    c.hr0 c.hrm c.hs0 c.hsm c.hMissing
  have hRow : y / 2 = t ∧ y % 2 = c.y := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    unfold Cell.y at hy ⊢
    exact ⟨by omega, by omega, by omega⟩
  have hCol : (x - 2 * m.val * t) / (2 * halfPeriod m) = q ∧
      (x - 2 * m.val * t) % (2 * halfPeriod m) = c.x := by
    apply (Int.ediv_emod_unique (by have := halfPeriod_pos m; omega)).mpr
    exact ⟨by omega, hX0, hXlt⟩
  have hx' : x = c.x + 2 * m.val * t + 2 * halfPeriod m * q := by omega
  have hCell : cellOf m x y = c := by
    rw [hx', hy]
    exact cellOf_lifted_cell m c t q
  simp only [profile, hCell, hRow.1, hCol.1]

/-- The full affine extension at every valid Cell and all signed period indices. -/
theorem profile_at_lifted_cell (m : Parameter) (ε : Fin 2) (c : Cell m) (t q : ℤ) :
    profile m ε (c.x + 2 * m.val * t + 2 * halfPeriod m * q) (2 * t + c.y) =
      representativeHeight m ε c - q * c.x + q * m.val * c.y -
        halfPeriod m * q ^ 2 + periodConstant m ε * q - t * c.y - t ^ 2 -
        (ε.val : ℤ) * t := by
  exact profile_of_reduction m ε _ _ c t q rfl (by ring)

/-- The physical function equals the source table on every valid representative. -/
theorem profile_at_cell (m : Parameter) (ε : Fin 2) (c : Cell m) :
    profile m ε c.x c.y = representativeHeight m ε c := by
  simpa using profile_at_lifted_cell m ε c 0 0

end FLattice.Auxiliary.MinusProfile
