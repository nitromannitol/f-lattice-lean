import FLattice.Auxiliary.PlusOddActiveRegion
import FLattice.Auxiliary.PlusOddSpecialValues
import FLattice.Auxiliary.PlusOddPeriods

/-!
# Two integer averages attach the odd negative-sign comparison point

Once strict comparison is known on the original active region, no enlarged
region or additional rank is necessary. Its point (-1,-1) forces a strict
bound at (-2,-1), which forces the same bound at (-2,0). The other incoming
values are bounded below by the explicit reference profile.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile

/-- The terminal point of the two-step attachment is in the original region. -/
theorem activePoint_added_successor_shift (m : Parameter) :
    activePoint m (-1) (-1) := by
  have hm := m.property
  let c : Cell m := ⟨0, m.val - 1, 1, 1,
    by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨c, ?_, -1, ?_, ?_⟩
  · simp [cellActive, c]
  · dsimp [Cell.x, c]
    ring
  · norm_num [Cell.y, c]

/-- The two horizontal inputs of (-2,-1) have zero reference height. -/
theorem profile_added_lower_inputs (m : Parameter) :
    profile m (-3) (-1) = 0 ∧ profile m (-1) (-1) = 0 := by
  have hLeft := profile_add_diagonal_period m (-3) (-1)
  have hRight := profile_add_diagonal_period m (-1) (-1)
  rw [show -3 + 2 * m.val = 2 * m.val - 3 by ring] at hLeft
  rw [show -1 + 2 * m.val = 2 * m.val - 1 by ring] at hRight
  norm_num only at hLeft hRight
  rw [profile_added_neighbor_left] at hLeft
  rw [profile_added_successor] at hRight
  omega

/-- A strict comparison on the original active region gives the negative
attachment bound by two native superharmonicity inequalities. -/
theorem one_le_added_point_of_active_strict_comparison
    (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLower : ∀ z : ℤ × ℤ, profile m z.1 z.2 ≤ h z)
    (hActive : ∀ x y : ℤ, activePoint m x y → profile m x y + 1 ≤ h (x, y)) :
    1 ≤ h (-2, 0) := by
  obtain ⟨hLeftValue, hRightValue⟩ := profile_added_lower_inputs m
  have hLeft := hLower (-3, -1)
  have hRight := hActive (-1) (-1) (activePoint_added_successor_shift m)
  have hUp := hLower (-2, 1)
  change profile m (-3) (-1) ≤ h (-3, -1) at hLeft
  change profile m (-2) 1 ≤ h (-2, 1) at hUp
  rw [hLeftValue] at hLeft
  rw [hRightValue] at hRight
  rw [profile_added_point_up] at hUp
  have hHorizontal := hSuperharmonic (-2) (-1)
  have hVertical := hSuperharmonic (-2) 0
  norm_num at hHorizontal hVertical
  omega

end FLattice.Auxiliary.PlusOddProfile
