import FLattice.Auxiliary.PlusEvenSpecialValues
import FLattice.Auxiliary.NegativeTriangle
import FLattice.Auxiliary.PlusEvenRegions
import FLattice.Auxiliary.PlusEvenCellCoset
import Mathlib.Tactic.FinCases

/-!
# Exact shifted even-plus values for the negative comparison

The arguments below retain the literal shift `(x - 4m, y - 2)`. They
evaluate the profile on the finite triangle and its incoming collar;
they do not assert a superharmonic comparison or recurrence theorem.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

open PlusEvenBulk NegativeTriangle

private theorem baseline_bit (t : ℤ) (e : Fin 2) :
    baseline (2 * t + (e.val : ℤ)) =
      -2 * t ^ 2 - 2 * (e.val : ℤ) * t + t - 1 := by
  fin_cases e <;> norm_num [baseline]
  · have h : 2 * t * (2 * t - 1) = (2 * t ^ 2 - t) * 2 := by ring
    rw [h, Int.mul_ediv_cancel _ (by norm_num)]
    ring
  · have h : (2 * t + 1) * (2 * t) = (2 * t ^ 2 + t) * 2 := by ring
    rw [h, Int.mul_ediv_cancel _ (by norm_num)]
    ring

private theorem shifted_lift (m : Parameter) (s t : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s ≤ m.val - 2) (ht : 0 ≤ t) (htm : t ≤ m.val - 1) :
    profile m (2 * s + 2 + (v.val : ℤ) - 4 * m.val)
      (2 * t + (e.val : ℤ) - 2) =
      representativeHeight e v (m.val + 1 - t) s +
      m.val ^ 2 - 2 * m.val * t + 2 * s + (v.val : ℤ) + 1 -
      m.val * (e.val : ℤ) - t * (e.val : ℤ) + (e.val : ℤ) - t ^ 2 + t := by
  have h := profile_at_lifted_cell m (m.val + 1 - t) s (t - 1) (-1) e v
    (by omega) (by omega) hs (by omega) (by omega)
  unfold halfPeriod at h
  norm_num at h
  ring_nf at h ⊢
  exact h

private theorem shifted_rectangle (m : Parameter) (s t : ℤ) (e v : Fin 2)
    (hs : 0 ≤ s) (hsm : s ≤ m.val - 2) (ht : 0 ≤ t) (htm : t ≤ m.val - 1)
    (hsum : (2 * s + 2 + (v.val : ℤ)) + (2 * t + (e.val : ℤ)) ≤ 2 * m.val + 2) :
    profile m (2 * s + 2 + (v.val : ℤ) - 4 * m.val)
      (2 * t + (e.val : ℤ) - 2) = baseline (2 * t + (e.val : ℤ)) +
      if 2 * m.val ≤ (2 * s + 2 + (v.val : ℤ)) + (2 * t + (e.val : ℤ))
      then 1 else 0 := by
  rw [shifted_lift m s t e v hs hsm ht htm, baseline_bit]
  have hr : m.val + 1 - t ≠ 0 := by omega
  fin_cases e <;> fin_cases v <;>
    norm_num [representativeHeight, hr, u00, u01, u10, u11, h10] at hsum ⊢ <;>
    simp only [h00, h01, h11] <;> ring_nf <;> omega

private theorem shifted_wedge (m : Parameter) (x y : ℤ)
    (hx : 2 ≤ x) (hxm : x ≤ 2 * m.val - 1)
    (hy : 0 ≤ y) (hym : y ≤ 2 * m.val - 1) (hsum : x + y ≤ 2 * m.val + 2) :
    profile m (x - 4 * m.val) (y - 2) =
      baseline y + if 2 * m.val ≤ x + y then 1 else 0 := by
  let s := (x - 2) / 2
  let t := y / 2
  let e := binaryState y
  let v := binaryState (x - 2)
  have he : (e.val : ℤ) = y % 2 := binaryState_val y
  have hv : (v.val : ℤ) = (x - 2) % 2 := binaryState_val (x - 2)
  have hx' : x = 2 * s + 2 + (v.val : ℤ) := by dsimp [s]; omega
  have hy' : y = 2 * t + (e.val : ℤ) := by dsimp [t]; omega
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hsm : s ≤ m.val - 2 := by dsimp [s]; omega
  have ht : 0 ≤ t := by dsimp [t]; omega
  have htm : t ≤ m.val - 1 := by dsimp [t]; omega
  rw [hx', hy']
  exact shifted_rectangle m s t e v hs hsm ht htm (by omega)

private theorem shifted_x_one (m : Parameter) (e : Fin 2) :
    profile m (1 - 4 * m.val) ((e.val : ℤ) - 2) = -1 := by
  have hm := m.property
  have h := profile_at_lifted_cell m m.val (m.val - 1) (-1) (-1) e 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [height_01_penultimate_right] at h
    norm_num at h
    unfold halfPeriod at h
    ring_nf at h ⊢
    exact h
  · rw [height_11_right m.val m.val hm (by omega)] at h
    norm_num at h
    unfold halfPeriod at h
    ring_nf at h ⊢
    exact h

private theorem shifted_left_one (m : Parameter) :
    profile m (1 - 4 * m.val) 0 = -2 := by
  have hm := m.property
  have h := profile_at_lifted_cell m (m.val - 1) (m.val - 1) 0 (-1) 0 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_01_wrapped_left m.val m.val (by omega)] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

/-- The full finite triangle has exactly the two indicated raised diagonals. -/
theorem negative_shift_triangle (m : Parameter) (x y : ℤ)
    (hx : 1 ≤ x) (hxm : x ≤ 2 * m.val - 1) (hy : 0 ≤ y)
    (hyx : y ≤ x) (hsum : x + y ≤ 2 * m.val + 1) :
    profile m (x - 4 * m.val) (y - 2) = baseline y +
      if x + y = 2 * m.val ∨ x + y = 2 * m.val + 1 then 1 else 0 := by
  have hm := m.property
  by_cases hx1 : x = 1
  · subst x
    have hyCases : y = 0 ∨ y = 1 := by omega
    rcases hyCases with rfl | rfl
    · have h := shifted_x_one m 0
      norm_num at h
      norm_num only [Int.reduceSub]
      rw [h, if_neg (by omega)]
      norm_num [baseline]
    · have h := shifted_x_one m 1
      norm_num at h
      norm_num only [Int.reduceSub]
      rw [h, if_neg (by omega)]
      norm_num [baseline]
  · rw [shifted_wedge m x y (by omega) hxm hy (by omega) (by omega)]
    congr 1
    split_ifs <;> omega

/-- Every nonexceptional point of the left diagonal collar has the baseline height. -/
theorem negative_shift_left_boundary (m : Parameter) (i : ℤ)
    (hi : 1 ≤ i) (him : i ≤ m.val - 1) :
    profile m (i - 4 * m.val) (i + 1 - 2) = baseline (i + 1) := by
  have hm := m.property
  by_cases hi1 : i = 1
  · subst i
    simpa [baseline] using shifted_left_one m
  · rw [shifted_wedge m i (i + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega), if_neg (by omega), add_zero]

/-- Every point of the right diagonal collar is one above the baseline. -/
theorem negative_shift_right_boundary (m : Parameter) (i : ℤ)
    (hi : m.val + 1 ≤ i) (him : i ≤ 2 * m.val - 1) :
    profile m (i - 4 * m.val) (2 * m.val + 2 - i - 2) =
      baseline (2 * m.val + 2 - i) + 1 := by
  have hm := m.property
  rw [shifted_wedge m i (2 * m.val + 2 - i) (by omega) him
    (by omega) (by omega) (by omega), if_pos (by omega)]

/-- The exceptional first point of the left collar is one below its baseline. -/
theorem negative_shift_left_zero (m : Parameter) :
    profile m (0 - 4 * m.val) (1 - 2) = -2 := by
  have hm := m.property
  have h := profile_at_lifted_cell m m.val (m.val - 1) (-1) (-1) 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_10_right m.val m.val hm (by omega)] at h
  norm_num at h
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

/-- The odd bottom collar includes exactly one corrected representative. -/
theorem negative_shift_bottom_boundary (m : Parameter) (i : ℤ)
    (hi : 1 ≤ i) (him : i ≤ 2 * m.val - 1) (hOdd : i % 2 = 1) :
    profile m (i - 4 * m.val) (-1 - 2) = if i = 1 then -1 else -2 := by
  have hm := m.property
  let s := (i - 1) / 2
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hsm : s < m.val := by dsimp [s]; omega
  have hi' : i = 2 * s + 1 := by dsimp [s]; omega
  have h := profile_at_lifted_cell m 0 s (-2) 0 1 1
    (by omega) (by omega) hs hsm (by omega)
  rw [height_11_row_zero s hs] at h
  norm_num at h
  rw [hi']
  simp only [show (2 * s + 1 = 1) ↔ s = 0 by omega]
  ring_nf at h ⊢
  exact h

/-- The point immediately left of the target origin has shifted height `-1`. -/
theorem negative_shift_left_of_origin (m : Parameter) :
    profile m (-1 - 4 * m.val) (0 - 2) = -1 := by
  have hm := m.property
  have h := profile_at_lifted_cell m m.val (m.val - 2) (-1) (-1) 0 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [height_01_eq, u01, show m.val - (m.val - 2) = 2 by omega] at h
  norm_num [h01] at h
  unfold halfPeriod at h
  ring_nf at h ⊢
  exact h

/-- The right source point is the original prescribed point after the shift. -/
theorem negative_shift_source (m : Parameter) :
    profile m (2 * m.val - 4 * m.val) (1 - 2) = 1 := by
  convert profile_prescribed_point m using 1
  congr 1
  ring

private theorem cell_fields_of_lift (m : Parameter) (x y r s k q : ℤ) (e v : Fin 2)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1) (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1))
    (hx : x = 2 * m.val * r + 2 * s + (v.val : ℤ) +
      2 * m.val * k + 2 * halfPeriod m * q)
    (hy : y = 2 * k + (e.val : ℤ)) :
    (cellOf m x y).r = r ∧ (cellOf m x y).s = s ∧
      (cellOf m x y).e = e ∧ (cellOf m x y).v = v := by
  let c : Cell m := ⟨r, s, e, v, hr0, hrm, hs0, hsm, hMissing⟩
  have hc : cellOf m x y = c := by
    rw [hx, hy]
    exact cellOf_lifted_cell m c k q
  rw [hc]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The signed reduction used for every ordinary triangle and diagonal point. -/
theorem negative_shift_rectangle_cell (m : Parameter) (x y : ℤ)
    (hx : 2 ≤ x) (hxm : x ≤ 2 * m.val - 1)
    (hy : 0 ≤ y) (hym : y ≤ 2 * m.val - 1) :
    (cellOf m (x - 4 * m.val) (y - 2)).r = m.val + 1 - y / 2 ∧
    (cellOf m (x - 4 * m.val) (y - 2)).s = (x - 2) / 2 ∧
    (cellOf m (x - 4 * m.val) (y - 2)).e = binaryState y ∧
    (cellOf m (x - 4 * m.val) (y - 2)).v = binaryState (x - 2) := by
  have he := binaryState_val y
  have hv := binaryState_val (x - 2)
  have hxd : x = 2 * ((x - 2) / 2) + 2 + ((binaryState (x - 2)).val : ℤ) := by omega
  have hyd : y = 2 * (y / 2) + ((binaryState y).val : ℤ) := by omega
  apply cell_fields_of_lift m _ _ (m.val + 1 - y / 2) ((x - 2) / 2)
    (y / 2 - 1) (-1) (binaryState y) (binaryState (x - 2))
    (by omega) (by omega) (by omega) (by omega) (by omega)
  · unfold halfPeriod
    nlinarith only [hxd]
  · omega

private theorem shifted_rectangle_not_prescribed (m : Parameter) (x y : ℤ)
    (hx : 2 ≤ x) (hxm : x ≤ 2 * m.val - 1)
    (hy : 0 ≤ y) (hym : y ≤ 2 * m.val - 1) :
    ¬cellPrescribed (cellOf m (x - 4 * m.val) (y - 2)) := by
  have hr := (negative_shift_rectangle_cell m x y hx hxm hy hym).1
  intro hp
  have hp0 := hp.1
  omega

/-- Every odd horizontal coordinate avoids the shifted prescribed coset. -/
theorem negative_shift_odd_not_prescribed (m : Parameter) (x y : ℤ)
    (hOdd : x % 2 = 1) :
    ¬cellPrescribed (cellOf m (x - 4 * m.val) (y - 2)) := by
  intro hp
  obtain ⟨a, b, hx, _⟩ := (cellPrescribed_cellOf_iff m _ _).mp hp
  have hEven : x = 2 * (m.val - (2 * m.val ^ 2 + 2 * m.val - 1) * a - m.val * b) := by
    nlinarith only [hx]
  rw [hEven] at hOdd
  omega

/-- No triangle point becomes a prescribed cell under the negative shift. -/
theorem negative_shift_triangle_not_prescribed (m : Parameter) (x y : ℤ)
    (hx : 1 ≤ x) (hxm : x ≤ 2 * m.val - 1) (hy : 0 ≤ y) (hyx : y ≤ x) :
    ¬cellPrescribed (cellOf m (x - 4 * m.val) (y - 2)) := by
  by_cases hx1 : x = 1
  · subst x
    exact negative_shift_odd_not_prescribed m 1 y (by decide)
  · exact shifted_rectangle_not_prescribed m x y (by omega) hxm hy (by omega)

/-- Every nonexceptional left-collar point avoids the shifted prescribed cell. -/
theorem negative_shift_left_boundary_not_prescribed (m : Parameter) (i : ℤ)
    (hi : 1 ≤ i) (him : i ≤ m.val - 1) :
    ¬cellPrescribed (cellOf m (i - 4 * m.val) (i + 1 - 2)) := by
  have hm := m.property
  by_cases hi1 : i = 1
  · subst i
    exact negative_shift_odd_not_prescribed m 1 2 (by decide)
  · exact shifted_rectangle_not_prescribed m i (i + 1)
      (by omega) (by omega) (by omega) (by omega)

/-- Every right-collar point avoids the shifted prescribed cell. -/
theorem negative_shift_right_boundary_not_prescribed (m : Parameter) (i : ℤ)
    (hi : m.val + 1 ≤ i) (him : i ≤ 2 * m.val - 1) :
    ¬cellPrescribed (cellOf m (i - 4 * m.val) (2 * m.val + 2 - i - 2)) := by
  have hm := m.property
  exact shifted_rectangle_not_prescribed m i (2 * m.val + 2 - i)
    (by omega) him (by omega) (by omega)

/-- The exceptional first left-collar point reduces to `10(m,m-1)`. -/
theorem negative_shift_left_zero_cell (m : Parameter) :
    (cellOf m (0 - 4 * m.val) (1 - 2)).r = m.val ∧
    (cellOf m (0 - 4 * m.val) (1 - 2)).s = m.val - 1 ∧
    (cellOf m (0 - 4 * m.val) (1 - 2)).e = 1 ∧
    (cellOf m (0 - 4 * m.val) (1 - 2)).v = 0 := by
  have hm := m.property
  apply cell_fields_of_lift m _ _ m.val (m.val - 1) (-1) (-1) 1 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  · norm_num
    unfold halfPeriod
    ring
  · norm_num

/-- The exceptional first left-collar point belongs to the stronger-gain region. -/
theorem negative_shift_left_zero_regionI (m : Parameter) :
    regionI (cellOf m (0 - 4 * m.val) (1 - 2)) := by
  obtain ⟨hr, hs, he, hv⟩ := negative_shift_left_zero_cell m
  have hm := m.property
  simp only [regionI, hr, hs, he, hv]
  norm_num
  omega

/-- The odd bottom collar has the exact corrected row-zero representatives. -/
theorem negative_shift_bottom_cell (m : Parameter) (i : ℤ)
    (hi : 1 ≤ i) (him : i ≤ 2 * m.val - 1) (hOdd : i % 2 = 1) :
    (cellOf m (i - 4 * m.val) (-1 - 2)).r = 0 ∧
    (cellOf m (i - 4 * m.val) (-1 - 2)).s = (i - 1) / 2 ∧
    (cellOf m (i - 4 * m.val) (-1 - 2)).e = 1 ∧
    (cellOf m (i - 4 * m.val) (-1 - 2)).v = 1 := by
  have hm := m.property
  apply cell_fields_of_lift m _ _ 0 ((i - 1) / 2) (-2) 0 1 1
    (by omega) (by omega) (by omega) (by omega) (by omega)
  · norm_num
    omega
  · norm_num

/-- All odd bottom-collar points after the first belong to Region I. -/
theorem negative_shift_bottom_regionI (m : Parameter) (i : ℤ)
    (hi : 3 ≤ i) (him : i ≤ 2 * m.val - 1) (hOdd : i % 2 = 1) :
    regionI (cellOf m (i - 4 * m.val) (-1 - 2)) := by
  obtain ⟨hr, hs, he, hv⟩ := negative_shift_bottom_cell m i (by omega) him hOdd
  simp only [regionI, hr, hs, he, hv]
  norm_num
  omega

end FLattice.Auxiliary.PlusEvenProfile
