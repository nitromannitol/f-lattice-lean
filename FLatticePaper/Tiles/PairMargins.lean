import FLatticePaper.Tiles.SiteBase

/-! Task 53, item 2 (the margin layer of the ordinary propagation). Parents `P = (d, n)` odd and `Q = (e, r)` even, proper,
with determinant `d r − n e = ±1`. The grade margins of the hand argument are integer inequalities in these parameters.

The first one: for the odd parent at `m = 1`, the `t` facet `E_t(P) = (2d + c)/(d + e)` (`c = d − n`) is below the inner margin
`h_t(P) + 1 = (c + 2)/2`. This is `2(2d + c) < (c + 2)(d + e)`. -/

namespace FLatticePaper.Tiles.PairMargins

theorem margin_t_odd_m1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hodd : (d + n) % 2 = 1) (hr : 0 < r)
    (hre : r < e) (heven : (e + r) % 2 = 0) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (2 * d + (d - n)) < ((d - n) + 2) * (d + e) := by
  have he3 : 3 ≤ e := by omega
  rcases (show d - n = 1 ∨ 2 ≤ d - n by omega) with hc | hc
  · have hn1 : n = d - 1 := by omega
    subst hn1
    have hk : d * (e - r) ≥ d := by nlinarith
    have hkey : e ≥ d - 1 := by
      rcases hdet with h | h
      · nlinarith
      · nlinarith
    have h3 : d + 2 < 3 * e := by omega
    rw [show d - (d - 1) = 1 by ring]
    nlinarith
  · have h1 : (d - n - 2) * d ≥ 0 := mul_nonneg (by omega) (by omega)
    have h2 : (d - n + 2) * (e - 3) ≥ 0 := mul_nonneg (by omega) (by omega)
    nlinarith

/-- A positive `n` with `n k = ±1` is `1`. -/
theorem pm_one_unit (n k : ℤ) (hn : 0 < n) (h : n * k = 1 ∨ n * k = -1) : n = 1 := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rcases h with h | h <;> simp at h
  have h1 : n ≤ 1 := by
    rcases h with h | h <;> rcases (show k ≥ 1 ∨ k ≤ -1 by omega) with hk | hk <;> nlinarith
  omega

/-- The even parent has odd numerator: `e + r` even and `dr − ne = ±1` force `r` odd. -/
theorem pm_r_odd (d n e r : ℤ) (heven : (e + r) % 2 = 0) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    r % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one r with h | h
  · exfalso
    obtain ⟨a, rfl⟩ : ∃ a, r = 2 * a := ⟨r / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, e = 2 * b := ⟨e / 2, by omega⟩
    have h2 : d * (2 * a) - n * (2 * b) = 2 * (d * a - n * b) := by ring
    rw [h2] at hdet
    omega
  · exact h

/-- The odd parent `t` facet at `m = 2`: `E_t(P) = (2d + 2c)/(2d + e) < (c + 2)/2`. -/
theorem margin_t_odd_m2 (d n e : ℤ) (hn : 0 < n) (hnd : n < d) (he : 0 < e) :
    2 * (2 * d + 2 * (d - n)) < ((d - n) + 2) * (2 * d + e) := by
  have h1 : (d - n) * (d - 2) ≥ 0 := mul_nonneg (by omega) (by omega)
  have h2 : (d - n) * e > 0 := mul_pos (by omega) he
  nlinarith

/-- The odd parent `s` facet at `m = 1`: `E_s(P) = (2c + 2d)/(d + e) < |2n − d| + 2`. -/
theorem margin_s_odd_m1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (d - n) + 2 * d < (|2 * n - d| + 2) * (d + e) := by
  rcases lt_trichotomy (2 * n) d with h | h | h
  · -- y = d − 2n ≥ 1
    rw [abs_of_neg (by omega : 2 * n - d < 0)]
    have h1 : (d - 2 * n - 1) * (d + e - 1) ≥ 0 := mul_nonneg (by omega) (by omega)
    nlinarith
  · -- d = 2n: then n = 1 and d = 2
    have hd : d = 2 * n := by omega
    subst hd
    have hk : n * (2 * r - e) = 1 ∨ n * (2 * r - e) = -1 := by
      rcases hdet with h' | h'
      · left; linarith [show (2 * n) * r - n * e = n * (2 * r - e) by ring]
      · right; linarith [show (2 * n) * r - n * e = n * (2 * r - e) by ring]
    have hn1 : n = 1 := pm_one_unit n _ hn hk
    subst hn1
    rw [show (2 * 1 : ℤ) - 2 * 1 = 0 by norm_num]
    norm_num
    omega
  · -- x = 2n − d ≥ 1
    rw [abs_of_pos (by omega : 0 < 2 * n - d)]
    have h1 : (2 * n - d - 1) * (d + e + 1) ≥ 0 := mul_nonneg (by omega) (by omega)
    nlinarith

/-- The odd parent `s` facet at `m = 2`: `E_s(P) = (2c + 4d)/(2d + e) < |2n − d| + 2`. -/
theorem margin_s_odd_m2 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (d - n) + 4 * d < (|2 * n - d| + 2) * (2 * d + e) := by
  rcases lt_trichotomy (2 * n) d with h | h | h
  · rw [abs_of_neg (by omega : 2 * n - d < 0)]
    have h1 : (d - 2 * n - 1) * (d) ≥ 0 := mul_nonneg (by omega) (by omega)
    have h2 : (d - 2 * n) * (e - 1) ≥ 0 := mul_nonneg (by omega) (by omega)
    nlinarith
  · have hd : d = 2 * n := by omega
    subst hd
    have hk : n * (2 * r - e) = 1 ∨ n * (2 * r - e) = -1 := by
      rcases hdet with h' | h'
      · left; linarith [show (2 * n) * r - n * e = n * (2 * r - e) by ring]
      · right; linarith [show (2 * n) * r - n * e = n * (2 * r - e) by ring]
    have hn1 : n = 1 := pm_one_unit n _ hn hk
    subst hn1
    norm_num
    omega
  · rw [abs_of_pos (by omega : 0 < 2 * n - d)]
    have h1 : (2 * n - d - 1) * d ≥ 0 := mul_nonneg (by omega) (by omega)
    have h2 : (2 * n - d) * e > 0 := mul_pos (by omega) (by omega)
    nlinarith

/-- The even parent `s` facet at `m = 1`: `E_s(Q) = (2f + 2e)/(d + e) < r + 2`, with `f = e − r`. -/
theorem margin_s_even_m1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (e - r) + 2 * e < (r + 2) * (d + e) := by
  rcases (show r = 1 ∨ 3 ≤ r by have := pm_r_odd d n e r heven hdet; omega) with h | h
  · subst h
    have hne : n * e ≤ d + 1 := by rcases hdet with h' | h' <;> linarith
    have he : e ≤ n * e := by nlinarith
    nlinarith
  · have h1 : (r - 2) * e ≥ 0 := mul_nonneg (by omega) (by omega)
    have h2 : (r + 2) * d ≥ 0 := mul_nonneg (by omega) (by omega)
    nlinarith

/-- The even parent `s` facet at `m = 2`: `E_s(Q) = (2f + 4e)/(2d + e) < r + 2`. -/
theorem margin_s_even_m2 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (e - r) + 4 * e < (r + 2) * (2 * d + e) := by
  rcases (show r = 1 ∨ r = 3 ∨ 5 ≤ r by have := pm_r_odd d n e r heven hdet; omega) with h | h | h
  · subst h
    have hne : n * e ≤ d + 1 := by rcases hdet with h' | h' <;> linarith
    have he : e ≤ n * e := by nlinarith
    nlinarith
  · subst h
    have hne : n * e ≤ 3 * d + 1 := by rcases hdet with h' | h' <;> linarith
    have he : e ≤ n * e := by nlinarith
    nlinarith
  · have h1 : (r - 4) * e ≥ 0 := mul_nonneg (by omega) (by omega)
    have h2 : (r + 2) * (2 * d) ≥ 0 := mul_nonneg (by omega) (by omega)
    nlinarith

/-- The wall identity for `p/q = 1/3`: `d(3r − e) − e(3n − d) = 3(dr − ne)`, and `3n − d` is odd. -/
theorem key_wall3 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e) (heven : (e + r) % 2 = 0)
    (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) (hU : 3 * r - e ≠ 0) :
    d * |3 * r - e| ≥ e - 3 := by
  have hid : d * (3 * r - e) - e * (3 * n - d) = 3 * (d * r - n * e) := by ring
  have hV : 3 * n - d ≠ 0 := by omega
  have he3 : 3 ≤ e := by omega
  have hd2 : 2 ≤ d := by omega
  have hε : -3 ≤ 3 * (d * r - n * e) ∧ 3 * (d * r - n * e) ≤ 3 := by
    rcases hdet with h | h <;> constructor <;> linarith
  obtain ⟨hε1, hε2⟩ := hε
  have he0 : (0:ℤ) ≤ e := by omega
  have hd0 : (0:ℤ) ≤ d := by omega
  rcases lt_or_gt_of_ne hU with hneg | hpos
  · rw [abs_of_neg (by omega : 3 * r - e < 0)]
    have hdU : d * (3 * r - e) ≤ -2 := by
      nlinarith [mul_nonneg hd0 (show (0:ℤ) ≤ -(3 * r - e) - 1 by omega)]
    rcases lt_or_gt_of_ne hV with hV1 | hV1
    · have heV : e * (3 * n - d) ≤ -e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ -(3 * n - d) - 1 by omega)]
      nlinarith
    · have heV : e * (3 * n - d) ≥ e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ (3 * n - d) - 1 by omega)]
      nlinarith
  · rw [abs_of_pos (by omega : 0 < 3 * r - e)]
    have hdU : d * (3 * r - e) ≥ 2 := by
      nlinarith [mul_nonneg hd0 (show (0:ℤ) ≤ (3 * r - e) - 1 by omega)]
    rcases lt_or_gt_of_ne hV with hV1 | hV1
    · have heV : e * (3 * n - d) ≤ -e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ -(3 * n - d) - 1 by omega)]
      nlinarith
    · have heV : e * (3 * n - d) ≥ e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ (3 * n - d) - 1 by omega)]
      nlinarith

/-- The wall identity for `p/q = 3/5`: `d(5r − 3e) − e(5n − 3d) = 5(dr − ne)`, with `5n − 3d` odd. -/
theorem key_wall5 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (_hr : 0 < r) (_hre : r < e) (heven : (e + r) % 2 = 0)
    (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) (he5 : 5 ≤ e) (hU : 5 * r - 3 * e ≠ 0) :
    d * |5 * r - 3 * e| ≥ e - 5 := by
  have hid : d * (5 * r - 3 * e) - e * (5 * n - 3 * d) = 5 * (d * r - n * e) := by ring
  have hV : 5 * n - 3 * d ≠ 0 := by omega
  have hd2 : 2 ≤ d := by omega
  have hε : -5 ≤ 5 * (d * r - n * e) ∧ 5 * (d * r - n * e) ≤ 5 := by
    rcases hdet with h | h <;> constructor <;> linarith
  obtain ⟨hε1, hε2⟩ := hε
  have he0 : (0:ℤ) ≤ e := by omega
  have hd0 : (0:ℤ) ≤ d := by omega
  rcases lt_or_gt_of_ne hU with hneg | hpos
  · rw [abs_of_neg (by omega : 5 * r - 3 * e < 0)]
    have hdU : d * (5 * r - 3 * e) ≤ -2 := by
      nlinarith [mul_nonneg hd0 (show (0:ℤ) ≤ -(5 * r - 3 * e) - 1 by omega)]
    rcases lt_or_gt_of_ne hV with hV1 | hV1
    · have heV : e * (5 * n - 3 * d) ≤ -e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ -(5 * n - 3 * d) - 1 by omega)]
      nlinarith
    · have heV : e * (5 * n - 3 * d) ≥ e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ (5 * n - 3 * d) - 1 by omega)]
      nlinarith
  · rw [abs_of_pos (by omega : 0 < 5 * r - 3 * e)]
    have hdU : d * (5 * r - 3 * e) ≥ 2 := by
      nlinarith [mul_nonneg hd0 (show (0:ℤ) ≤ (5 * r - 3 * e) - 1 by omega)]
    rcases lt_or_gt_of_ne hV with hV1 | hV1
    · have heV : e * (5 * n - 3 * d) ≤ -e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ -(5 * n - 3 * d) - 1 by omega)]
      nlinarith
    · have heV : e * (5 * n - 3 * d) ≥ e := by
        nlinarith [mul_nonneg he0 (show (0:ℤ) ≤ (5 * n - 3 * d) - 1 by omega)]
      nlinarith

/-- **Even parent, lower wall, `m = 1`.** `E_t(Q) = (3e − r)·2/(d+e)` against `|3r − e| + 4`. -/
theorem margin_t_even_lower_m1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (3 * e - r) < (|3 * r - e| + 4) * (d + e) := by
  have hd2 : 2 ≤ d := by omega
  by_cases h3 : 3 * r - e = 0
  · have he : e = 3 * r := by omega
    subst he
    have hr1 : r = 1 := pm_one_unit r (d - 3 * n) hr (by
      rcases hdet with h | h
      · left; linarith [show d * r - n * (3 * r) = r * (d - 3 * n) by ring]
      · right; linarith [show d * r - n * (3 * r) = r * (d - 3 * n) by ring])
    subst hr1
    norm_num
    omega
  · have hk := key_wall3 d n e r hn hnd hr hre heven hodd hdet h3
    have hZ : 1 ≤ |3 * r - e| := Int.one_le_abs h3
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ |3 * r - e| - 1) (by linarith : (0:ℤ) ≤ e)]

/-- **Even parent, lower wall, `m = 2`.** `E_t(Q) = (4e − 2r)/(2d+e)` against `|3r − e| + 4`. -/
theorem margin_t_even_lower_m2 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    8 * e - 4 * r < (|3 * r - e| + 4) * (2 * d + e) := by
  have hd2 : 2 ≤ d := by omega
  have he0 : (0:ℤ) ≤ e := by omega
  by_cases h3 : 3 * r - e = 0
  · have he : e = 3 * r := by omega
    subst he
    have hr1 : r = 1 := pm_one_unit r (d - 3 * n) hr (by
      rcases hdet with h | h
      · left; linarith [show d * r - n * (3 * r) = r * (d - 3 * n) by ring]
      · right; linarith [show d * r - n * (3 * r) = r * (d - 3 * n) by ring])
    subst hr1
    norm_num
    omega
  · have hk := key_wall3 d n e r hn hnd hr hre heven hodd hdet h3
    rcases lt_or_gt_of_ne h3 with hneg | hpos
    · rw [abs_of_neg (by omega : 3 * r - e < 0)] at hk ⊢
      rcases (show e - 3 * r = 1 ∨ 2 ≤ e - 3 * r by omega) with h1 | h2
      · have he' : e = 3 * r + 1 := by omega
        subst he'
        nlinarith
      · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ e - 3 * r - 2) he0]
    · rw [abs_of_pos (by omega : 0 < 3 * r - e)] at hk ⊢
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ 3 * r - e - 1) he0]

/-- If `5r = 3e` then the determinant forces `(e, r) = (5, 3)`. -/
theorem wall_eq5 (d n e r : ℤ) (_hn : 0 < n) (hr : 0 < r) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1)
    (h5 : 5 * r - 3 * e = 0) : e = 5 ∧ r = 3 := by
  have he : e % 5 = 0 := by omega
  obtain ⟨s, rfl⟩ : ∃ s, e = 5 * s := ⟨e / 5, by omega⟩
  have hr3 : r = 3 * s := by omega
  subst hr3
  have hk : s * (3 * d - 5 * n) = 1 ∨ s * (3 * d - 5 * n) = -1 := by
    rcases hdet with h | h
    · left; linarith [show d * (3 * s) - n * (5 * s) = s * (3 * d - 5 * n) by ring]
    · right; linarith [show d * (3 * s) - n * (5 * s) = s * (3 * d - 5 * n) by ring]
  have hs1 : s = 1 := pm_one_unit s (3 * d - 5 * n) (by omega) hk
  subst hs1
  norm_num

/-- **Even parent, upper wall, `m = 1`.** `E_t(Q) = (3e − r)·2/(d+e)` against `|5r − 3e| + 4`. -/
theorem margin_t_even_upper_m1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    2 * (3 * e - r) < (|5 * r - 3 * e| + 4) * (d + e) := by
  have hd2 : 2 ≤ d := by omega
  have he0 : (0:ℤ) ≤ e := by omega
  by_cases h5 : 5 * r - 3 * e = 0
  · obtain ⟨he5, hr3⟩ := wall_eq5 d n e r hn hr hdet h5
    subst he5
    subst hr3
    norm_num
    omega
  · rcases lt_or_gt_of_ne h5 with hneg | hpos
    · rw [abs_of_neg (by omega : 5 * r - 3 * e < 0)]
      nlinarith [mul_nonneg (by nlinarith : (0:ℤ) ≤ 3 * e - 5 * r + 4) (by linarith : (0:ℤ) ≤ d - 2),
        mul_nonneg (by linarith : (0:ℤ) ≤ 3 * e - 5 * r - 1) he0]
    · rw [abs_of_pos (by omega : 0 < 5 * r - 3 * e)]
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ 5 * r - 3 * e + 4) (by linarith : (0:ℤ) ≤ d - 2),
        mul_nonneg (by linarith : (0:ℤ) ≤ 5 * r - 3 * e - 1) he0]

/-- **Even parent, upper wall, `m = 2`.** `E_t(Q) = (4e − 2r)/(2d+e)` against `|5r − 3e| + 4`. -/
theorem margin_t_even_upper_m2 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1 ∨ d * r - n * e = -1) :
    8 * e - 4 * r < (|5 * r - 3 * e| + 4) * (2 * d + e) := by
  have hd2 : 2 ≤ d := by omega
  have he0 : (0:ℤ) ≤ e := by omega
  have hrodd := pm_r_odd d n e r heven hdet
  have heodd : e % 2 = 1 := by omega
  by_cases h5 : 5 * r - 3 * e = 0
  · obtain ⟨he5, hr3⟩ := wall_eq5 d n e r hn hr hdet h5
    subst he5
    subst hr3
    norm_num
    omega
  · rcases (show e = 3 ∨ 5 ≤ e by omega) with he3 | he5'
    · subst he3
      have hr1 : r = 1 := by omega
      subst hr1
      norm_num
      omega
    · have hk := key_wall5 d n e r hn hnd hr hre heven hodd hdet he5' h5
      rcases lt_or_gt_of_ne h5 with hneg | hpos
      · rw [abs_of_neg (by omega : 5 * r - 3 * e < 0)] at hk ⊢
        rcases (show 3 * e - 5 * r = 1 ∨ 2 ≤ 3 * e - 5 * r by omega) with h1 | h2
        · have hd' : d * (3 * e - 5 * r) = d := by rw [h1, mul_one]
          have he7 : 7 ≤ e := by omega
          nlinarith
        · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ 3 * e - 5 * r - 2) he0]
      · rw [abs_of_pos (by omega : 0 < 5 * r - 3 * e)] at hk ⊢
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ 5 * r - 3 * e - 1) he0]

end FLatticePaper.Tiles.PairMargins
