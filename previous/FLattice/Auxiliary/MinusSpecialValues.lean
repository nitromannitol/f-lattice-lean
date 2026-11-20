import FLattice.Auxiliary.MinusCoordinates

/-!
# Exact origin and prescribed-coset values of the minus profiles

The parameter is m >= 2. Every value is evaluated through the actual signed
Cell lift, retaining both the odd top-row height and the minus affine gauge.
No superharmonicity, comparison or transport assertion is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

/-- Both minus profiles have value one at the origin. -/
theorem profile_origin (m : Parameter) (ε : Fin 2) : profile m ε 0 0 = 1 := by
  have hm := m.property
  let c : Cell m := ⟨0, 0, 0, 0, by omega, by omega, by omega, by omega, by omega⟩
  have h := profile_at_cell m ε c
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · simpa [Cell.x, Cell.y, c, representativeHeight] using h
  · simpa [Cell.x, Cell.y, c, representativeHeight,
      show (3 : ℤ) ≤ 2 * m.val by omega] using h

/-- The full prescribed coset has the source value for every signed index pair. -/
theorem profile_prescribed_coset (m : Parameter) (ε : Fin 2) (a b : ℤ) :
    profile m ε
      ((if ε = 0 then 2 * m.val + 2 else -1) -
        (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b)
      ((if ε = 0 then 1 else 0) - 2 * m.val * a - 2 * b) =
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 - (m.val + 1) * a - b) := by
  have hm := m.property
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · let c : Cell m := ⟨1, 1, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
    have h := profile_at_lifted_cell m 0 c (-m.val * a - b) (-a)
    norm_num [Cell.x, Cell.y, c, representativeHeight, periodConstant] at h ⊢
    unfold halfPeriod at h ⊢
    ring_nf at h ⊢
    exact h
  · let c : Cell m := ⟨m.val + 1, m.val - 2, 0, 1,
      by omega, by omega, by omega, by omega, by omega⟩
    have hHeight : representativeHeight m 1 c = -halfPeriod m := by
      have hRow : m.val + 1 ≠ 0 := by omega
      norm_num [representativeHeight, c, hRow,
        show 2 * (m.val + 1) - 3 - (2 * (m.val - 2) + 1) = (2 : ℤ) by ring,
        show 2 * (m.val - 2) + 1 - 2 * m.val + 3 = (0 : ℤ) by ring]
      unfold halfPeriod
      ring
    have h := profile_at_lifted_cell m 1 c (-m.val * a - b) (-a - 1)
    rw [hHeight] at h
    norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
    unfold halfPeriod at h ⊢
    ring_nf at h ⊢
    exact h

/-- The points D0=(2m+2,1) and D1=(-1,0) both have prescribed height one. -/
theorem profile_prescribed_point (m : Parameter) (ε : Fin 2) :
    profile m ε (if ε = 0 then 2 * m.val + 2 else -1) (if ε = 0 then 1 else 0) = 1 := by
  simpa using profile_prescribed_coset m ε 0 0

/-- The shifted even root has value zero, including the distinct m=2 reduction. -/
theorem profile_even_shifted_origin (m : Parameter) :
    profile m 0 (4 * m.val + 4) 2 = 0 := by
  have hm := m.property
  by_cases hmTwo : m.val = 2
  · let c : Cell m := ⟨2, 0, 0, 0, by omega, by omega, by omega, by omega, by omega⟩
    have h := profile_at_lifted_cell m 0 c 1 0
    norm_num [Cell.x, Cell.y, c, representativeHeight, hmTwo] at h ⊢
    exact h
  · let c : Cell m := ⟨1, 2, 0, 0, by omega, by omega, by omega, by omega, by omega⟩
    have h := profile_at_lifted_cell m 0 c 1 0
    norm_num [Cell.x, Cell.y, c, representativeHeight] at h
    convert h using 1
    congr 1
    ring

/-- The shifted odd root has value one for the entire parameter range. -/
theorem profile_odd_shifted_origin (m : Parameter) : profile m 1 (-2) 0 = 1 := by
  have hm := m.property
  let c : Cell m := ⟨m.val + 1, m.val - 2, 0, 0,
    by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 1 c = 1 - halfPeriod m := by
    have hRow : m.val + 1 ≠ 0 := by omega
    norm_num [representativeHeight, c, hRow,
      show 2 * (m.val + 1) - 3 - 2 * (m.val - 2) = (3 : ℤ) by ring,
      show 2 * (m.val - 2) - 2 * m.val + 3 = (-1 : ℤ) by ring]
    unfold halfPeriod
    ring
  have h := profile_at_lifted_cell m 1 c 0 (-1)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h
  unfold halfPeriod at h
  ring_nf at h
  exact h

end FLattice.Auxiliary.MinusProfile
