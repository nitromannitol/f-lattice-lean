import FLattice.Auxiliary.PlusOddCellData

/-!
# The odd prescribed cell and its physical coset

Both directions use explicit signed lifts in the common period geometry.
The prescribed set is identified from its coordinates, independently of
the profile's values, deficits or clock.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The canonical prescribed-cell predicate is exactly the signed coset
`D - C(a,b)` with `D = (-1,0)`. -/
theorem cellPrescribed_cellOf_iff (m : Parameter) (x y : ℤ) :
    cellPrescribed (cellOf m x y) ↔ ∃ a b : ℤ,
      x = -1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -2 * m.val * a - 2 * b := by
  constructor
  · rintro ⟨hr, hs, he, hv⟩
    obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
    simp only [Cell.x, Cell.y, hr, hs, he, hv] at hx hy
    norm_num at hx hy
    refine ⟨-q - 1, m.val * (q + 1) - k, ?_, ?_⟩
    · rw [hx]
      unfold halfPeriod
      ring
    · rw [hy]
      ring
  · rintro ⟨a, b, rfl, rfl⟩
    have hm := m.property
    let p : Cell m := ⟨m.val + 1, m.val - 2, 0, 1,
      by omega, by omega, by omega, by omega, by omega⟩
    have hLift := cellOf_lifted_cell m p (-m.val * a - b) (-a - 1)
    have hX : p.x + 2 * m.val * (-m.val * a - b) + 2 * halfPeriod m * (-a - 1) =
        -1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b := by
      dsimp [p, Cell.x, halfPeriod]
      ring
    have hY : 2 * (-m.val * a - b) + p.y = -2 * m.val * a - 2 * b := by
      dsimp [p, Cell.y]
      ring
    rw [hX, hY] at hLift
    rw [hLift]
    exact ⟨rfl, rfl, rfl, rfl⟩

end FLattice.Auxiliary.PlusOddProfile
