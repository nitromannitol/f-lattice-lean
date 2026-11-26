import FLatticePaper.Plane.Induction.FreeVOrdinate

/-! # A lattice gap for the odd free V roots

For a site `z` with `t = tGrade z`, `s = sGrade z`, the identity `T · z.2 = n s − L t` (`FreeVOrdinate.T_mul_ordinate`) forces
`n s − L (t + T)` to be a multiple of `T`. If `t + T ∈ [2n + d, 2d + n − 2]` and `s ∈ [3n + 2 − d, d + n − 2]`, the multiple lies strictly
between `−2T` and `0`, so it is `−T`, and then `L (t + T) = n s + T` contradicts the two bounds. No such `z` exists. -/

namespace FLatticePaper.VGap

open FLatticePaper FLatticePaper.Induction

theorem no_gap (frame : ChildFrame) (z : Site)
    (ht1 : 2 * frame.child.num + frame.child.den ≤ frame.tGrade z + frame.child.periodDenominator)
    (ht2 : frame.tGrade z + frame.child.periodDenominator ≤ 2 * frame.child.den + frame.child.num - 2)
    (hs1 : 3 * frame.child.num + 2 - frame.child.den ≤ frame.sGrade z)
    (hs2 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2) : False := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hy := FreeVOrdinate.T_mul_ordinate frame z
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  have hL0 : (0 : ℤ) ≤ frame.child.den + frame.child.num := by omega
  have hn0' : (0 : ℤ) ≤ frame.child.num := by omega
  -- the multiple: T * (z.2 - L) = n s - L (t + T)
  have hm : frame.child.periodDenominator * (z.2 - (frame.child.den + frame.child.num))
      = frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * (frame.tGrade z + frame.child.periodDenominator) := by
    linear_combination hy
  -- the bounds on the right side: it lies strictly between -2T and 0
  have hup : frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * (frame.tGrade z + frame.child.periodDenominator) < 0 := by
    have h1 := mul_le_mul_of_nonneg_left ht1 hL0
    have h2 := mul_le_mul_of_nonneg_left hs2 hn0'
    nlinarith
  have hlow : -(2 * frame.child.periodDenominator) <
      frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * (frame.tGrade z + frame.child.periodDenominator) := by
    have h1 := mul_le_mul_of_nonneg_left hs1 hn0'
    have h2 := mul_le_mul_of_nonneg_left ht2 hL0
    rw [hTd] at h2 ⊢
    nlinarith
  set m := z.2 - (frame.child.den + frame.child.num) with hmdef
  have hm_lt : m < 0 := by
    by_contra h
    have h' : 0 ≤ m := not_lt.mp h
    have := mul_nonneg hTpos.le h'
    linarith
  have hm_gt : -2 < m := by
    by_contra h
    have h' : m ≤ -2 := not_lt.mp h
    have := mul_le_mul_of_nonneg_left h' hTpos.le
    linarith
  have hm_eq : m = -1 := by omega
  rw [hm_eq] at hm
  -- -T = n s - L (t + T), so L (t + T) = n s + T, and the bounds on both sides contradict
  have h1 := mul_le_mul_of_nonneg_left ht1 hL0
  have h2 := mul_le_mul_of_nonneg_left hs2 hn0'
  rw [hTd] at hm h1
  nlinarith

/-- For an odd free V root the grade `t` is at most `n + 1`: if `t ≥ n + 2` (with `t ≤ d`, `3n + 2 - d ≤ s ≤ d + n - 2`), the
multiple `T · z.2 = n s - L t` would lie strictly between `-T` and `0`. -/
theorem t_le_n_plus_one (frame : ChildFrame) (z : Site)
    (ht : frame.tGrade z ≤ frame.child.den)
    (hs1 : 3 * frame.child.num + 2 - frame.child.den ≤ frame.sGrade z)
    (hs2 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2) :
    frame.tGrade z ≤ frame.child.num + 1 := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hy := FreeVOrdinate.T_mul_ordinate frame z
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  have hL0 : (0 : ℤ) ≤ frame.child.den + frame.child.num := by omega
  have hn0' : (0 : ℤ) ≤ frame.child.num := by omega
  by_contra hcon
  have h2 : frame.child.num + 2 ≤ frame.tGrade z := by omega
  have hup : frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * frame.tGrade z < 0 := by
    have h1 := mul_le_mul_of_nonneg_left hs2 hn0'
    have h3 := mul_le_mul_of_nonneg_left h2 hL0
    nlinarith
  have hlow : -frame.child.periodDenominator <
      frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * frame.tGrade z := by
    have h1 := mul_le_mul_of_nonneg_left hs1 hn0'
    have h3 := mul_le_mul_of_nonneg_left ht hL0
    rw [hTd]
    nlinarith
  rw [← hy] at hup hlow
  by_cases hyn : 0 ≤ z.2
  · have := mul_nonneg hTpos.le hyn
    linarith
  · have hyn' : z.2 ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left hyn' hTpos.le
    linarith

end FLatticePaper.VGap
