import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Task w3, step 1(b)(B): the parent t-grade range of the free H arc, per phase and parity (integer core).

With `L = d + n`, the key identity of the word is `L · t_p = (D + N) · t + ε · u` (`HWeb.key_identity_tp`, `u = x + y`), and
`(D + N) n = N L − ε`, `(D + N) d = D L + ε` (from `ε = N d − D n`). The free H bounds on the child grades `t, u` are
`2 ≤ t ≤ L − 2`, `0 ≤ u ≤ L − 2` (even sites) and `n ≤ t ≤ d`, `0 ≤ u ≤ L − 1` (odd sites) (`HWeb.m_range_even/odd`).
Each lemma below is the integer step for one phase and parity; the query shift `t_p(x) = t_p(w) − (1 − W) ε` is applied later. -/

namespace FLatticePaper.TpRange

/-- **Phase zero, even sites** (`ε = −1`): `0 ≤ t_p ≤ r − 1`, hence `1 ≤ t_p(x) = t_p + 1 ≤ r` for the query. -/
theorem tp_even_W0 (D N L t u tp : ℤ) (hD : 0 < D) (hN : 0 ≤ N) (hL : 0 < L)
    (key : L * tp = (D + N) * t + (-1) * u) (ht1 : t ≤ L - 2) (hu0 : 0 ≤ u)
    (htp0 : 0 ≤ tp) : 0 ≤ tp ∧ tp ≤ D + N - 1 := by
  refine ⟨htp0, ?_⟩
  have hr : 0 ≤ D + N := by omega
  have h1 : (D + N) * t ≤ (D + N) * (L - 2) := mul_le_mul_of_nonneg_left ht1 hr
  have h2 : L * tp < L * (D + N) := by nlinarith
  have h3 : tp < D + N := lt_of_mul_lt_mul_left h2 hL.le
  omega

/-- **Phase zero, odd sites** (`ε = −1`, `(D+N) n = N L + 1`, `(D+N) d = D L − 1`): `N ≤ t_p ≤ D − 1`, hence
`N + 1 ≤ t_p(x) ≤ D` for the query. -/
theorem tp_odd_W0 (D N L n d t u tp : ℤ) (hD : 0 < D) (hN : 0 ≤ N) (hL : 0 < L)
    (hrn : (D + N) * n = N * L + 1) (hrd : (D + N) * d = D * L - 1)
    (key : L * tp = (D + N) * t + (-1) * u) (ht0 : n ≤ t) (ht1 : t ≤ d) (hu0 : 0 ≤ u) (hu1 : u ≤ L - 1) :
    N ≤ tp ∧ tp ≤ D - 1 := by
  have hr : 0 ≤ D + N := by omega
  have h1 : (D + N) * t ≤ (D + N) * d := mul_le_mul_of_nonneg_left ht1 hr
  have h2 : (D + N) * n ≤ (D + N) * t := mul_le_mul_of_nonneg_left ht0 hr
  constructor
  · have h3 : L * (N - 1) < L * tp := by nlinarith
    have h4 : N - 1 < tp := lt_of_mul_lt_mul_left h3 hL.le
    omega
  · have h3 : L * tp < L * D := by nlinarith
    have h4 : tp < D := lt_of_mul_lt_mul_left h3 hL.le
    omega

/-- **Phase one, even sites** (`ε = +1`): `1 ≤ t_p ≤ r`, and `t_p(x) = t_p` for the query. -/
theorem tp_even_W1 (D N L t u tp : ℤ) (hD : 0 < D) (hN : 0 ≤ N) (hL : 0 < L)
    (key : L * tp = (D + N) * t + 1 * u) (ht0 : 2 ≤ t) (ht1 : t ≤ L - 2) (hu0 : 0 ≤ u) (hu1 : u ≤ L - 2) :
    1 ≤ tp ∧ tp ≤ D + N := by
  have hr : 0 ≤ D + N := by omega
  have h1 : (D + N) * t ≤ (D + N) * (L - 2) := mul_le_mul_of_nonneg_left ht1 hr
  have h0 : 0 < L * tp := by nlinarith
  constructor
  · by_contra hc
    have : tp ≤ 0 := by omega
    have : L * tp ≤ 0 := by nlinarith
    omega
  · have h2 : L * tp < L * (D + N + 1) := by nlinarith
    have h3 : tp < D + N + 1 := lt_of_mul_lt_mul_left h2 hL.le
    omega

/-- **Phase one, odd sites** (`ε = +1`, `(D+N) n = N L − 1`, `(D+N) d = D L + 1`): `N ≤ t_p ≤ D + 1`, and `t_p(x) = t_p`. -/
theorem tp_odd_W1 (D N L n d t u tp : ℤ) (hD : 0 < D) (hN : 0 ≤ N) (hL : 2 ≤ L)
    (hrn : (D + N) * n = N * L - 1) (hrd : (D + N) * d = D * L + 1)
    (key : L * tp = (D + N) * t + 1 * u) (ht0 : n ≤ t) (ht1 : t ≤ d) (hu0 : 0 ≤ u) (hu1 : u ≤ L - 1) :
    N ≤ tp ∧ tp ≤ D + 1 := by
  have hr : 0 ≤ D + N := by omega
  have hL0 : 0 < L := by omega
  have h1 : (D + N) * t ≤ (D + N) * d := mul_le_mul_of_nonneg_left ht1 hr
  have h2 : (D + N) * n ≤ (D + N) * t := mul_le_mul_of_nonneg_left ht0 hr
  constructor
  · have h3 : L * (N - 1) < L * tp := by nlinarith
    have h4 : N - 1 < tp := lt_of_mul_lt_mul_left h3 hL0.le
    omega
  · have h3 : L * tp ≤ L * (D + 1) := by nlinarith
    have h4 : tp ≤ D + 1 := le_of_mul_le_mul_left h3 hL0
    exact h4

end FLatticePaper.TpRange
