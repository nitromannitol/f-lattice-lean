import FLatticePaper.Plane.Induction.ParentWeb

/-! Task 60, the native V path of the odd parent (fix Q3.md paragraphs 8–9).

With `N, D` the odd parent, `r = D + N`, `B = D² + 2DN − N²`, `t_p(x) = N x₁ − D x₂`, and `v_l = (−b'_l, 2l − 1 − b'_l)`,
`b'_l = ⌊(D − N) l / D⌋`:
* (1) the floors agree: `⌊(d − n) l / d⌋ = ⌊(D − N) l / D⌋` for `1 ≤ l < D` (the child and the parent vertices coincide);
* (2) the odd native vertices with `1 ≤ l ≤ D − 1` lie in the box `N − D + 1 ≤ x₁ ≤ 0`, `0 ≤ x₂ ≤ D + N − 1`, and on this box
  `r − B ≤ t_p ≤ 0` (the endpoint `V_p + I = (N − D + 1, D + N − 1)` has `t_p = r − B`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- Integer division on a window of length `B`: `x ∈ (−B, 0)` gives `x / B = −1`. -/
theorem ediv_eq_neg_one_of_range (x B : ℤ) (hB : 0 < B) (h1 : -B < x) (h2 : x < 0) : x / B = -1 := by
  have hA := Int.ediv_mul_le x hB.ne'
  have hC := Int.lt_ediv_add_one_mul_self x hB
  have h3 : x / B ≤ -1 := by
    by_contra hc
    have h0 : 0 ≤ x / B := by omega
    nlinarith [mul_nonneg h0 hB.le]
  have h4 : -1 ≤ x / B := by
    by_contra hc
    have h5 : x / B ≤ -2 := by omega
    nlinarith [mul_le_mul_of_nonneg_right (show x / B + 1 ≤ -1 by omega) hB.le]
  omega

/-- The residue `q` of (1): `D q = d r + ε l` with `r ∈ [1, D)` and `0 < q < d`. -/
theorem vBlock_floor_arith (D N d n ε l : ℤ) (hD : 0 < D) (hdD : D < d) (hε : ε = 1 ∨ ε = -1)
    (hEps : ε = N * d - D * n) (hl1 : 1 ≤ l) (hl2 : l < D) :
    (d - n) * l / d = (D - N) * l / D := by
  have hr0 := Int.emod_nonneg ((D - N) * l) hD.ne'
  have hr1' := Int.emod_lt_of_pos ((D - N) * l) hD
  have hdef : (D - N) * l % D = (D - N) * l - D * ((D - N) * l / D) := Int.emod_def _ _
  set bp := (D - N) * l / D with hbp
  set r := (D - N) * l % D with hr
  set q := (d - n) * l - d * bp with hq
  have key : D * q = d * r + ε * l := by
    rw [hq, hdef]
    rcases hε with h | h <;> subst h <;> linear_combination (-l) * hEps
  have hd0 : 0 ≤ d := by omega
  have hr1 : 1 ≤ r := by
    by_contra hc
    have hr00 : r = 0 := by omega
    rw [hr00, mul_zero, zero_add] at key
    have hq0 : q = 0 := by
      rcases hε with h | h <;> subst h <;>
        rcases lt_trichotomy q 0 with hq' | hq' | hq' <;> nlinarith
    rw [hq0, mul_zero] at key
    rcases hε with h | h <;> subst h <;> omega
  have hqpos : 0 < q := by
    by_contra hc
    have hq' : q ≤ 0 := by omega
    rcases hε with h | h <;> subst h <;>
      nlinarith [mul_nonneg hd0 (show (0 : ℤ) ≤ r - 1 by omega)]
  have hqlt : q < d := by
    by_contra hc
    have hq' : d ≤ q := by omega
    rcases hε with h | h <;> subst h <;>
      nlinarith [mul_nonneg hD.le (show (0 : ℤ) ≤ q - d by omega),
        mul_nonneg hd0 (show (0 : ℤ) ≤ D - 1 - r by omega)]
  have hdne : d ≠ 0 := by omega
  have hM : (d - n) * l = q + bp * d := by rw [hq]; ring
  rw [hM, Int.add_mul_ediv_right _ _ hdne, Int.ediv_eq_zero_of_lt hqpos.le hqlt, zero_add]

/-- The box `N − D + 1 ≤ x₁ ≤ 0`, `0 ≤ x₂ ≤ D + N − 1` carries `r − B ≤ t_p ≤ 0`. -/
theorem vbox_tp_bounds (D N x1 x2 : ℤ) (hD : 0 ≤ D) (hN : 0 ≤ N) (h1 : N - D + 1 ≤ x1) (h2 : x1 ≤ 0)
    (h3 : 0 ≤ x2) (h4 : x2 ≤ D + N - 1) :
    (D + N) - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x1 - D * x2 ∧ N * x1 - D * x2 ≤ 0 := by
  constructor
  · nlinarith [mul_nonneg hN (sub_nonneg.2 h1), mul_nonneg hD (sub_nonneg.2 h4)]
  · nlinarith [mul_nonneg hN (neg_nonneg.2 h2), mul_nonneg hD h3]

/-- The odd native vertices `v_l = (−b'_l, 2l − 1 − b'_l)`, `1 ≤ l ≤ D − 1`, lie in the box. -/
theorem odd_vertex_in_box (D N l : ℤ) (hD : 0 < D) (hN0 : 0 ≤ N) (hND : N < D) (hl1 : 1 ≤ l) (hl2 : l < D) :
    N - D + 1 ≤ -((D - N) * l / D) ∧ -((D - N) * l / D) ≤ 0 ∧
      0 ≤ 2 * l - 1 - (D - N) * l / D ∧ 2 * l - 1 - (D - N) * l / D ≤ D + N - 1 := by
  have hA := Int.ediv_mul_le ((D - N) * l) hD.ne'
  have hC := Int.lt_ediv_add_one_mul_self ((D - N) * l) hD
  set bp := (D - N) * l / D with hbp
  have hpos : 0 ≤ (D - N) * l := by nlinarith
  have hbp0 : 0 ≤ bp := Int.ediv_nonneg hpos hD.le
  have hbpD : bp ≤ D - N - 1 := by
    by_contra hc
    have h5 : D - N ≤ bp := by omega
    nlinarith [mul_le_mul_of_nonneg_right h5 hD.le,
      mul_pos (show (0 : ℤ) < D - N by omega) (show (0 : ℤ) < D - l by omega)]
  have hbpl : bp ≤ l := by
    by_contra hc
    have h5 : l + 1 ≤ bp := by omega
    nlinarith [mul_le_mul_of_nonneg_right h5 hD.le, mul_nonneg hN0 (show (0 : ℤ) ≤ l by omega)]
  have hbpl2 : 2 * l - D - N ≤ bp := by
    by_contra hc
    have h5 : bp + 1 ≤ 2 * l - D - N := by omega
    nlinarith [mul_le_mul_of_nonneg_right h5 hD.le,
      mul_pos (show (0 : ℤ) < D - l by omega) (show (0 : ℤ) < D + N by omega)]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- (1) at the frame level: the child's and the parent's floors agree for `1 ≤ l < D`. -/
theorem vBlock_floor_agree (frame : ChildFrame) (l : ℤ) (hl1 : 1 ≤ l) (hl2 : l < frame.parents.odd.den) :
    (frame.child.den - frame.child.num) * l / frame.child.den =
      (frame.parents.odd.den - frame.parents.odd.num) * l / frame.parents.odd.den := by
  have hD : 0 < frame.parents.odd.den := frame.valid.odd_bounds.1
  have hE : 0 < frame.parents.even.den := frame.valid.even_bounds.1
  have hcd : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  exact vBlock_floor_arith frame.parents.odd.den frame.parents.odd.num frame.child.den frame.child.num frame.eps l
    hD (by omega) frame.eps_unit frame.eps_eq hl1 hl2

/-- (2) the odd native vertices `v_l`, `1 ≤ l ≤ D − 1`, satisfy `r − B ≤ t_p(v_l) ≤ 0`. -/
theorem odd_vertex_tp_bounds (D N l : ℤ) (hD : 0 < D) (hN0 : 0 ≤ N) (hND : N < D) (hl1 : 1 ≤ l) (hl2 : l < D) :
    (D + N) - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * (-((D - N) * l / D)) - D * (2 * l - 1 - (D - N) * l / D) ∧
      N * (-((D - N) * l / D)) - D * (2 * l - 1 - (D - N) * l / D) ≤ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := odd_vertex_in_box D N l hD hN0 hND hl1 hl2
  exact vbox_tp_bounds D N _ _ hD.le hN0 h1 h2 h3 h4

end FLatticePaper.Induction
