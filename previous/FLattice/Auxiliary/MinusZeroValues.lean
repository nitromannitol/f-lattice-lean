import FLattice.Auxiliary.MinusCoordinates
import FLattice.Auxiliary.MinusZeroAverages

/-!
# Fourteen exact values for the general-minus zero-threshold contradiction

Every value is derived from an explicit valid Cell and signed lift. The
fixed averaging theorem is then consumed with the three global lower
comparisons, rather than assuming any of these fourteen values of h.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile

private theorem zero_value_0 (m : Parameter) :
    profile m 0 (4 * m.val) (-1) = 0 := by
  have hm := m.property
  let c : Cell m := ⟨3, 0, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 0 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (-1) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_1 (m : Parameter) :
    profile m 1 (-3) (-3) = 0 := by
  have hm := m.property
  let c : Cell m := ⟨1, m.val - 2, 1, 1, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 1 c = 0 := by
    norm_num [representativeHeight, c]
    omega
  have h := profile_at_lifted_cell m 1 c (-2) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_2 (m : Parameter) :
    profile m 0 (4 * m.val + 1) (1) = 1 := by
  have hm := m.property
  let c : Cell m := ⟨2, 0, 1, 1, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (0) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_3 (m : Parameter) :
    profile m 0 (0) (-3) = -1 := by
  have hm := m.property
  let c : Cell m := ⟨2, 0, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (-2) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_4 (m : Parameter) :
    profile m 1 (-2) (-1) = 1 := by
  have hm := m.property
  let c : Cell m := ⟨0, m.val - 1, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 1 c = 0 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 1 c (-1) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_5 (m : Parameter) :
    profile m 0 (4 * m.val + 2) (2) = 0 := by
  have hm := m.property
  let c : Cell m := ⟨1, 1, 0, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (1) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_6 (m : Parameter) :
    profile m 0 (0) (-1) = 1 := by
  have hm := m.property
  let c : Cell m := ⟨1, 0, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (-1) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_7 (m : Parameter) :
    profile m 0 (4 * m.val + 2) (3) = -1 := by
  have hm := m.property
  let c : Cell m := ⟨1, 1, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (1) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_8 (m : Parameter) :
    profile m 0 (4 * m.val + 3) (3) = -1 := by
  have hm := m.property
  let c : Cell m := ⟨1, 1, 1, 1, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (1) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_9 (m : Parameter) :
    profile m 0 (4 * m.val + 2) (5) = -5 := by
  have hm := m.property
  let c : Cell m := ⟨0, 1, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (2) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_10 (m : Parameter) :
    profile m 1 (-1) (3) = -3 := by
  have hm := m.property
  let c : Cell m := ⟨m.val, m.val - 2, 1, 1, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 1 c = -m.val ^ 2 + m.val := by
    norm_num [representativeHeight, c]
    omega
  have h := profile_at_lifted_cell m 1 c (1) (-1)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

private theorem zero_value_11 (m : Parameter) :
    profile m 0 (1) (1) = 1 := by
  have hm := m.property
  let c : Cell m := ⟨0, 0, 1, 1, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (0) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem zero_value_12 (m : Parameter) :
    profile m 0 (2) (3) = -2 := by
  have hm := m.property
  let c : Cell m := ⟨m.val + 1, 0, 1, 0, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = -m.val ^ 2 + 2 * m.val := by
    norm_num [representativeHeight, c, show m.val + 1 ≠ 0 by omega,
      show m.val ≠ 0 by omega, max_eq_left (show 0 ≤ m.val by omega),
      max_eq_left (show 0 ≤ m.val + 1 - 2 by omega)]
    ring
  have h := profile_at_lifted_cell m 0 c (1) (-1)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

private theorem zero_value_13 (m : Parameter) :
    profile m 0 (1) (0) = 1 := by
  have hm := m.property
  let c : Cell m := ⟨0, 0, 0, 1, by omega, by omega, by omega, by omega, by omega⟩
  have hHeight : representativeHeight m 0 c = 1 := by
    norm_num [representativeHeight, c]
  have h := profile_at_lifted_cell m 0 c (0) (0)
  rw [hHeight] at h
  norm_num [Cell.x, Cell.y, c, periodConstant] at h ⊢
  ring_nf at h ⊢
  exact h

/-- The three source lower comparisons force a positive origin for every
m>=2. All fourteen initial bounds are supplied internally by the profiles. -/
theorem one_le_origin_of_three_profiles
    (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hOrigin : 0 ≤ h (0, 0))
    (hA : ∀ x y : ℤ, profile m 0 (x + 4 * m.val + 4) (y + 2) ≤ h (x, y))
    (hB : ∀ x y : ℤ, profile m 1 (x - 1) y - 1 ≤ h (x, y))
    (hC : ∀ x y : ℤ, profile m 0 x y - 1 ≤ h (x, y)) :
    1 ≤ h (0, 0) := by
  apply one_le_origin_of_fourteen_bounds h hSuperharmonic hOrigin
  · have hBound := hA (-4) (-3)
    have hValue := zero_value_0 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hB (-2) (-3)
    have hValue := zero_value_1 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hA (-3) (-1)
    have hValue := zero_value_2 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hC (0) (-3)
    have hValue := zero_value_3 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hB (-1) (-1)
    have hValue := zero_value_4 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hA (-2) (0)
    have hValue := zero_value_5 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hC (0) (-1)
    have hValue := zero_value_6 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hA (-2) (1)
    have hValue := zero_value_7 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hA (-1) (1)
    have hValue := zero_value_8 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hA (-2) (3)
    have hValue := zero_value_9 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hB (0) (3)
    have hValue := zero_value_10 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hC (1) (1)
    have hValue := zero_value_11 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hC (2) (3)
    have hValue := zero_value_12 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega
  · have hBound := hC (1) (0)
    have hValue := zero_value_13 m
    ring_nf at hBound hValue
    rw [hValue] at hBound
    omega

end FLattice.Auxiliary.MinusProfile
