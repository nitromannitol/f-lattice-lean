import FLattice.Auxiliary.PlusEvenRegions

/-!
# The prescribed cell and the physical prescribed coset

The equivalence is proved by explicit signed lifts in both directions. It
uses no profile values or deficit classification as a definition of the coset.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- The canonical prescribed-cell predicate is exactly the source coset. -/
theorem cellPrescribed_cellOf_iff (m : Parameter) (x y : ℤ) :
    cellPrescribed (cellOf m x y) ↔ ∃ a b : ℤ,
      x = -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b ∧
      y = -1 - 2 * m.val * a - 2 * b := by
  constructor
  · rintro ⟨hr, hs, he, hv⟩
    obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
    simp only [Cell.x, Cell.y, hr, hs, he, hv] at hx hy
    norm_num at hx hy
    refine ⟨-q, m.val * q - k - 1, ?_, ?_⟩
    · rw [hx]
      unfold halfPeriod
      ring
    · rw [hy]
      ring
  · rintro ⟨a, b, rfl, rfl⟩
    have hm := m.property
    let p : Cell m := ⟨0, 0, 1, 0,
      by omega, by omega, by omega, by omega, by omega⟩
    have hLift := cellOf_lifted_cell m p (-1 - m.val * a - b) (-a)
    have hX : p.x + 2 * m.val * (-1 - m.val * a - b) + 2 * halfPeriod m * (-a) =
        -2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b := by
      dsimp [p, Cell.x, halfPeriod]
      ring
    have hY : 2 * (-1 - m.val * a - b) + p.y = -1 - 2 * m.val * a - 2 * b := by
      dsimp [p, Cell.y]
      ring
    rw [hX, hY] at hLift
    rw [hLift]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The physical origin belongs to the first region. -/
theorem regionI_cellOf_origin (m : Parameter) : regionI (cellOf m 0 0) := by
  have hm := m.property
  let c : Cell m := ⟨0, 0, 0, 0,
    by omega, by omega, by omega, by omega, by omega⟩
  have hLift := cellOf_lifted_cell m c 0 0
  norm_num [Cell.x, Cell.y, c] at hLift
  rw [hLift]
  simp [regionI]

end FLattice.Auxiliary.PlusEvenProfile
