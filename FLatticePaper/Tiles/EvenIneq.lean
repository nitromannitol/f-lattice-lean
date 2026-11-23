import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Task 53, item 2 (covering reduction), section 13: polynomial facet inequalities of the even child (`X = 2P + Q`, `μ_X = 1`).

Each lemma is a fact about the admissible pairs `P = (d, n)` (odd, `d + n` odd) and `Q = (e, r)` (even, `e + r` even) with
`d r − n e = ±1`. Hypothesis `3 ≤ d` excludes the single family `P = (2,1)` (the exceptional family of HAND_THEOREM §2), for which the
real corner facets fail and an integer argument is needed instead. The integer forms are used with `D = 2d + e` (the den of `X`),
after clearing the denominator `β = e / D`. -/

namespace FLatticePaper.Tiles.EvenIneq

theorem B_ineq (d n e r : ℤ) (hd : 0 < d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) : 4 * e < (r + 1) * (2 * d + e) := by
  have key : d * ((r + 1) * (2 * d + e)) = (n * e + 1 + d) * (2 * d + e) := by
    linear_combination (2 * d + e) * hdet
  have h1 : (e + 1 + d) * (2 * d + e) ≤ (n * e + 1 + d) * (2 * d + e) := by
    apply mul_le_mul_of_nonneg_right _ (by omega)
    nlinarith
  have h2 : 4 * e * d < d * ((r + 1) * (2 * d + e)) := by
    rw [key]
    nlinarith [sq_nonneg (e - d), sq_nonneg d]
  exact lt_of_mul_lt_mul_left (by linarith [h2]) hd.le

/-- `A1`: when `e ≤ 2r`, with `d ≥ 3` (the `P = (2,1)` family is excluded). -/
theorem A1_ineq (d n e r : ℤ) (hd : 3 ≤ d) (hn : 1 ≤ n) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0) (hle : e ≤ 2 * r) :
    4 * e < (2 * r + 1 - e) * (2 * d + e) := by
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * r - e := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by omega
  have he : e = 2 * r - m := by omega
  subst he
  have hrm : r * (d - 2 * n) = 1 - n * m := by linear_combination hdet
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with h0 | h1 | h2 | h3
  · -- m = 0: e = 2r, parity forces r = 1, then d - 2n = 1 is consistent but e + r = 3 is odd
    subst h0
    have hr1 : r = 1 := by
      rcases lt_trichotomy (d - 2 * n) 0 with h | h | h
      · nlinarith
      · nlinarith
      · nlinarith
    subst hr1
    omega
  · subst h1
    have hdn : d < 2 * n := by
      by_contra hc
      push Not at hc
      nlinarith
    have hrle : r ≤ n - 1 := by nlinarith
    nlinarith
  · subst h2
    have hdn : d < 2 * n := by
      by_contra hc
      push Not at hc
      nlinarith
    have hr2 : r ≤ 2 * n - 1 := by nlinarith
    nlinarith
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ m - 3 by omega) (show (0:ℤ) ≤ 2 * r - m by omega)]


/-- `A2`: when `e ≥ 2r`. -/
theorem A2_ineq (d n e r : ℤ) (hd : 3 ≤ d) (hn : 1 ≤ n) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0) (hge : 2 * r ≤ e) :
    4 * e < (e + 1 - 2 * r) * (2 * d + e) := by
  obtain ⟨p, hp⟩ : ∃ p, p = e - 2 * r := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by omega
  have he : e = 2 * r + p := by omega
  subst he
  have hp1 : 1 ≤ p := by
    by_contra hc
    have : p = 0 := by omega
    subst this
    have hr1 : r = 1 := by
      have hk : r * (d - 2 * n) = 1 := by linear_combination hdet
      rcases lt_trichotomy (d - 2 * n) 0 with h | h | h
      · nlinarith
      · nlinarith
      · nlinarith
    subst hr1
    omega
  have hk : r * (d - 2 * n) = 1 + n * p := by linear_combination hdet
  have hk1 : 1 ≤ d - 2 * n := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith [mul_nonneg (show (0:ℤ) ≤ p by omega) (show (0:ℤ) ≤ d - 2 * n - 1 by omega)]

/-- `C1`: when `e ≤ 3r`. -/
theorem C1_ineq (d n e r : ℤ) (hd : 3 ≤ d) (hn : 1 ≤ n) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (hle : e ≤ 3 * r) :
    4 * e < (3 * r - e + 2) * (2 * d + e) := by
  obtain ⟨q, hq⟩ : ∃ q, q = 3 * r - e := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by omega
  have he : 3 * r = e + q := by omega
  rw [← hq]
  rcases lt_or_ge e (2 * d) with h | h
  · nlinarith [mul_nonneg hq0 (show (0:ℤ) ≤ 2 * d + e by omega)]
  · have h3 : d - 3 * n ≤ -1 := by
      have h1 : e * (d - 3 * n) ≤ 3 := by nlinarith
      have hne : d - 3 * n ≠ 0 := by omega
      by_contra hc
      push Not at hc
      have : 1 ≤ d - 3 * n := by omega
      nlinarith
    have hdq : d * q = 3 + e * (3 * n - d) := by nlinarith
    have hq2 : 2 ≤ q := by
      by_contra hc
      push Not at hc
      have : q ≤ 1 := by omega
      nlinarith
    nlinarith [mul_nonneg (show (0:ℤ) ≤ q - 2 by omega) (show (0:ℤ) ≤ 2 * d + e by omega)]

/-- `C2`: when `e ≥ 3r`. -/
theorem C2_ineq (d n e r : ℤ) (hd : 3 ≤ d) (hn : 1 ≤ n) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hge : 3 * r ≤ e) :
    4 * e < (e - 3 * r + 2) * (2 * d + e) := by
  obtain ⟨q, hq⟩ : ∃ q, q = e - 3 * r := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by omega
  have he : e = 3 * r + q := by omega
  rw [← hq]
  rcases lt_or_ge e (2 * d) with h | h
  · nlinarith [mul_nonneg hq0 (show (0:ℤ) ≤ 2 * d + e by omega)]
  · have hdq : d * q = e * (d - 3 * n) - 3 := by nlinarith
    have hk : 1 ≤ d - 3 * n := by
      by_contra hc
      push Not at hc
      nlinarith
    have hdq2 : e - 3 ≤ d * q := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hdq2 (show (0:ℤ) ≤ 2 * d + e by omega)]

end FLatticePaper.Tiles.EvenIneq
