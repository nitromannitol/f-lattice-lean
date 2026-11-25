import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.EPolicyLap

/-! # The W1 forcing at the pure-threes children (task 72, W1 base; lead's option (a))

For the child `1/d`, `d = 2k+3`, the reciprocal field `reciprocalField k` (the standard field of `3^k`). Its strict interior
`StrictInterior 1 d` (the W1 grades with `n = 1`, `T = d² + 2d − 1`) is the hexagon
`1 ≤ y ≤ d`, `3 − d ≤ x ≤ d − 1`, `2 ≤ x + y ≤ d + 1` (`strictInterior_hexagon`). The proof uses the identities
`T·y = s − (d+1)t` and `T·x = (d−1)t + d·s` with `t = x − dy`, `s = (d+1)x + (d−1)y`.
-/

namespace FLatticePaper.W1Reciprocal


open FLatticePaper FLatticePaper.W1

/-- Even strict-interior points lie in the hexagon (forward direction). -/
theorem hex_even_fwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 0)
    (h1 : d - 1 - (d ^ 2 + 2 * d - 1) < x - d * y) (h2 : x - d * y < 2)
    (h3 : 2 < (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1) :
    1 ≤ y ∧ y ≤ d ∧ 3 - d ≤ x ∧ x ≤ d - 1 ∧ 2 ≤ x + y ∧ x + y ≤ d + 1 := by
  have hT : (d ^ 2 + 2 * d - 1) * y = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
  have hA : x - d * y ≤ 1 := by linarith
  have hB : 3 ≤ (d + 1) * x + (d - 1) * y := by linarith
  have hC : (d + 1) * x + (d - 1) * y ≤ d ^ 2 + 2 * d - 2 := by linarith
  have hD : d - (d ^ 2 + 2 * d - 1) ≤ x - d * y := by linarith
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  -- y ≥ 1
  have hy1 : 1 ≤ y := by
    by_contra hcon
    rcases (show y = 0 ∨ y ≤ -1 by omega) with hy | hy
    · subst hy
      have hx1 : x ≤ 1 := by linarith
      have hx2 : 1 ≤ x := by
        by_contra hc
        have : x ≤ 0 := by omega
        nlinarith
      have hx : x = 1 := by omega
      subst hx
      norm_num at hpar
    · have hT0 : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy hT0, mul_le_mul_of_nonneg_left hA hd1]
  -- y ≤ d
  have hyd : y ≤ d := by
    by_contra hcon
    have hy2 : d + 1 ≤ y := by omega
    rcases (show y = d + 1 ∨ d + 2 ≤ y by omega) with hy | hy
    · subst hy
      have hx1 : x ≤ 1 := by nlinarith
      have hx2 : 1 ≤ x := by nlinarith
      have hx : x = 1 := by omega
      subst hx
      have : (d + 1) % 2 = 0 := by omega
      omega
    · have hT0 : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hy hT0, mul_le_mul_of_nonneg_left hD hd1]
  -- x ≥ 3 - d
  have hxlo : 3 - d ≤ x := by
    by_contra hc
    have hc' : x ≤ 2 - d := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  -- x ≤ d - 1
  have hxhi : x ≤ d - 1 := by
    by_contra hc
    have hc' : d ≤ x := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  -- 2 ≤ x + y
  have hsum2 : 2 ≤ x + y := by
    by_contra hc
    have hc' : x + y ≤ 0 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  -- x + y ≤ d + 1
  have hsumhi : x + y ≤ d + 1 := by
    by_contra hc
    have hc' : d + 2 ≤ x + y := by omega
    have hc'' : d + 3 ≤ x + y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc'' hd1]
  exact ⟨hy1, hyd, hxlo, hxhi, hsum2, hsumhi⟩


/-- Odd strict-interior points lie in the hexagon. -/
theorem hex_odd_fwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 1)
    (h1 : d - (d ^ 2 + 2 * d - 1) < x - d * y) (h2 : x - d * y < 1)
    (h3 : d - 1 < (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1 + 3 - d) :
    1 ≤ y ∧ y ≤ d ∧ 3 - d ≤ x ∧ x ≤ d - 1 ∧ 2 ≤ x + y ∧ x + y ≤ d + 1 := by
  have hT : (d ^ 2 + 2 * d - 1) * y = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
  have hA : x - d * y ≤ 0 := by linarith
  have hB : d ≤ (d + 1) * x + (d - 1) * y := by linarith
  have hC : (d + 1) * x + (d - 1) * y ≤ d ^ 2 + 2 * d + 2 - d := by linarith
  have hD : d - (d ^ 2 + 2 * d - 1) + 1 ≤ x - d * y := by linarith
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  have hT0 : (0 : ℤ) ≤ d ^ 2 + 2 * d - 1 := by nlinarith
  have hy1 : 1 ≤ y := by
    by_contra hcon
    have hy0 : y ≤ 0 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hy0 hT0, mul_le_mul_of_nonneg_left hA hd1]
  have hyd : y ≤ d := by
    by_contra hcon
    have hy2 : d + 1 ≤ y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hy2 hT0, mul_le_mul_of_nonneg_left hD hd1]
  have hxlo : 3 - d ≤ x := by
    by_contra hc
    have hc' : x ≤ 2 - d := by omega
    have hyd' : (d - 1) * y ≤ (d - 1) * d := mul_le_mul_of_nonneg_left hyd (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  have hxhi : x ≤ d - 1 := by
    by_contra hc
    have hc' : d ≤ x := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  have hsum2 : 2 ≤ x + y := by
    by_contra hc
    have hc' : x + y ≤ 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  have hsumhi : x + y ≤ d + 1 := by
    by_contra hc
    have hc' : d + 2 ≤ x + y := by omega
    nlinarith [mul_le_mul_of_nonneg_left hc' hd1]
  exact ⟨hy1, hyd, hxlo, hxhi, hsum2, hsumhi⟩

/-- The hexagon gives the even strict-interior inequalities. -/
theorem hex_even_bwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 0)
    (hy1 : 1 ≤ y) (hyd : y ≤ d) (hxlo : 3 - d ≤ x) (hxhi : x ≤ d - 1) (hs2 : 2 ≤ x + y) (hss : x + y ≤ d + 1) :
    d - 1 - (d ^ 2 + 2 * d - 1) < x - d * y ∧ x - d * y < 2 ∧
      2 < (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1 := by
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  have hdy : d * 1 ≤ d * y := mul_le_mul_of_nonneg_left hy1 (by linarith)
  have hdyd : d * y ≤ d * d := mul_le_mul_of_nonneg_left hyd (by linarith)
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rcases (show x + y = 2 ∨ 3 ≤ x + y by omega) with h | h
    · have hx : x = 2 - y := by omega
      have hyd' : y ≤ d - 1 := by
        by_contra hc
        have : y = d := by omega
        subst this
        omega
      nlinarith [mul_le_mul_of_nonneg_left hyd' hd1]
    · nlinarith [mul_le_mul_of_nonneg_left h hd1]
  · rcases (show y = 1 ∨ 2 ≤ y by omega) with h | h
    · subst h
      nlinarith [mul_le_mul_of_nonneg_left hxhi hd1]
    · nlinarith [mul_le_mul_of_nonneg_left hss hd1, mul_le_mul_of_nonneg_left hxhi hd1]

/-- The hexagon gives the odd strict-interior inequalities. -/
theorem hex_odd_bwd {d x y : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (hpar : (x + y) % 2 = 1)
    (hy1 : 1 ≤ y) (hyd : y ≤ d) (hxlo : 3 - d ≤ x) (hxhi : x ≤ d - 1) (hs2 : 2 ≤ x + y) (hss : x + y ≤ d + 1) :
    d - (d ^ 2 + 2 * d - 1) < x - d * y ∧ x - d * y < 1 ∧
      d - 1 < (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y < d ^ 2 + 2 * d - 1 + 3 - d := by
  have hd1 : (0 : ℤ) ≤ d + 1 := by linarith
  have hdy : d * 1 ≤ d * y := mul_le_mul_of_nonneg_left hy1 (by linarith)
  have hdyd : d * y ≤ d * d := mul_le_mul_of_nonneg_left hyd (by linarith)
  have hss' : x + y ≤ d := by omega
  have hs3 : 3 ≤ x + y := by omega
  refine ⟨by nlinarith, by nlinarith, by nlinarith [mul_le_mul_of_nonneg_left hs3 hd1], ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hss' hd1]

/-- The strict interior of the child `1/d` (`n = 1`, `d` odd, `d ≥ 3`) is the hexagon. -/
theorem strictInterior_hexagon {d : ℤ} (hd : 3 ≤ d) (hdo : d % 2 = 1) (x y : ℤ) :
    StrictInterior 1 d (x, y) ↔
      (1 ≤ y ∧ y ≤ d ∧ 3 - d ≤ x ∧ x ≤ d - 1 ∧ 2 ≤ x + y ∧ x + y ≤ d + 1) := by
  unfold StrictInterior w1b w1T w1t w1a w1s w1h w1c
  simp only [EvenSite]
  by_cases hpar : (x + y) % 2 = 0
  · simp only [hpar, if_true]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      norm_num at h1 h2 h3 h4
      exact hex_even_fwd hd hdo hpar (by linarith) (by linarith) (by linarith) (by linarith)
    · rintro ⟨hy1, hyd, hxlo, hxhi, hs2, hss⟩
      have := hex_even_bwd hd hdo hpar hy1 hyd hxlo hxhi hs2 hss
      norm_num
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2.1], by linarith [this.2.2.2]⟩
  · have hpar1 : (x + y) % 2 = 1 := by omega
    simp only [hpar, if_false]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      norm_num at h1 h2 h3 h4
      exact hex_odd_fwd hd hdo hpar1 (by linarith) (by linarith) (by linarith) (by linarith)
    · rintro ⟨hy1, hyd, hxlo, hxhi, hs2, hss⟩
      have := hex_odd_bwd hd hdo hpar1 hy1 hyd hxlo hxhi hs2 hss
      norm_num
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2.1], by linarith [this.2.2.2]⟩


end FLatticePaper.W1Reciprocal
