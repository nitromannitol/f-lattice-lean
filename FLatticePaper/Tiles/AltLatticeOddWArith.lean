import Mathlib

/-! # Arithmetic of the contact `(Q^+, P^{-,1} + W)` of the odd alternate child, `W₁` even -/

namespace FLatticePaper.Tiles.AltLatticeOddWArith

set_option maxHeartbeats 400000 in
/-- Even parity: `t_q(z) ≥ min(2n₂, d₂ - n₂)`. -/
theorem gq_even (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2)
    (he : n1 * d2 - n2 * d1 = -1)
    (p1 : min (2 * n1) (d1 - n1) ≤ n1 * z1 - d1 * z2) (p3 : 0 ≤ (d1 + n1) * z1 + (d1 - n1) * z2) :
    min (2 * n2) (d2 - n2) ≤ n2 * z1 - d2 * z2 := by
  -- `T_p z₁ = (d₁ - n₁) t_p + d₁ σ_p > 0`
  have hT : (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * z1 = (d1 - n1) * (n1 * z1 - d1 * z2) + d1 * ((d1 + n1) * z1 + (d1 - n1) * z2) := by ring
  have hTp : 0 < d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2 := by nlinarith
  have ha : 1 ≤ min (2 * n1) (d1 - n1) := le_min (by omega) (by omega)
  have hz : 0 < z1 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sub_pos.2 h2).le (by linarith : (0 : ℤ) ≤ n1 * z1 - d1 * z2)]
  -- transfer: `d₁ t_q = d₂ t_p + z₁`
  have htr : d1 * (n2 * z1 - d2 * z2) = d2 * (n1 * z1 - d1 * z2) + z1 := by linear_combination (-z1) * he
  -- `d₂ a_p ≥ d₁ a_q - 2`
  have hmin : d1 * min (2 * n2) (d2 - n2) - 2 ≤ d2 * min (2 * n1) (d1 - n1) := by
    rcases le_total (2 * n1) (d1 - n1) with h | h <;> rcases le_total (2 * n2) (d2 - n2) with k | k <;>
      simp only [min_eq_left h, min_eq_right h, min_eq_left k, min_eq_right k] <;> nlinarith
  by_contra hc
  push Not at hc
  have : d1 * (n2 * z1 - d2 * z2) ≤ d1 * (min (2 * n2) (d2 - n2) - 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
  nlinarith [mul_le_mul_of_nonneg_left p1 (by omega : (0 : ℤ) ≤ d2)]

set_option maxHeartbeats 400000 in
/-- Odd parity: `t_q(z) ≥ n₂`. -/
theorem gq_odd (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2)
    (he : n1 * d2 - n2 * d1 = -1)
    (p1 : n1 ≤ n1 * z1 - d1 * z2) (p3 : min (d1 - n1) (3 * n1 - d1) ≤ (d1 + n1) * z1 + (d1 - n1) * z2) :
    n2 ≤ n2 * z1 - d2 * z2 := by
  have hT : (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * z1 = (d1 - n1) * (n1 * z1 - d1 * z2) + d1 * ((d1 + n1) * z1 + (d1 - n1) * z2) := by ring
  have htr : d1 * (n2 * z1 - d2 * z2) = d2 * (n1 * z1 - d1 * z2) + z1 := by linear_combination (-z1) * he
  by_contra hc
  push Not at hc
  have hz : z1 ≤ 1 - d1 := by nlinarith [mul_le_mul_of_nonneg_left p1 (by omega : (0 : ℤ) ≤ d2)]
  have hTp : 0 < d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2 := by nlinarith
  have k := mul_le_mul_of_nonneg_left hz hTp.le
  rcases min_choice (d1 - n1) (3 * n1 - d1) with hm | hm <;> rw [hm] at p3
  · nlinarith [mul_le_mul_of_nonneg_left p1 (sub_pos.2 h2).le, mul_pos h1 h1, mul_pos (sub_pos.2 h2) h1]
  · nlinarith [mul_le_mul_of_nonneg_left p1 (sub_pos.2 h2).le, mul_pos h1 h1, mul_pos (sub_pos.2 h2) h1,
      mul_pos (mul_pos (sub_pos.2 h2) h1) (by omega : (0 : ℤ) < d1), mul_pos (mul_pos h1 h1) (by omega : (0 : ℤ) < d1)]

set_option maxHeartbeats 400000 in
/-- Even parity: `t_p(z) ≤ d₁ + n₁ - min(2n₁, d₁ - n₁)`. -/
theorem gp_even (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2)
    (he : n1 * d2 - n2 * d1 = -1)
    (p1 : min (2 * n1) (d1 - n1) ≤ n1 * z1 - d1 * z2) (p3 : 0 ≤ (d1 + n1) * z1 + (d1 - n1) * z2)
    (q2 : n2 * z1 - d2 * z2 ≤ d2 + n2 - min (2 * n2) (d2 - n2)) :
    n1 * z1 - d1 * z2 ≤ d1 + n1 - min (2 * n1) (d1 - n1) := by
  have hT : (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * z1 = (d1 - n1) * (n1 * z1 - d1 * z2) + d1 * ((d1 + n1) * z1 + (d1 - n1) * z2) := by ring
  have hTp : 0 < d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2 := by nlinarith
  have ha : 1 ≤ min (2 * n1) (d1 - n1) := le_min (by omega) (by omega)
  have hz : 0 < z1 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sub_pos.2 h2).le (by linarith : (0 : ℤ) ≤ n1 * z1 - d1 * z2)]
  have htr : d1 * (n2 * z1 - d2 * z2) = d2 * (n1 * z1 - d1 * z2) + z1 := by linear_combination (-z1) * he
  have hmin : d2 * min (2 * n1) (d1 - n1) - d1 * min (2 * n2) (d2 - n2) < d2 := by
    rcases le_total (2 * n1) (d1 - n1) with h | h <;> rcases le_total (2 * n2) (d2 - n2) with k | k <;>
      simp only [min_eq_left h, min_eq_right h, min_eq_left k, min_eq_right k] <;> nlinarith
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_left q2 (by omega : (0 : ℤ) ≤ d1),
    mul_le_mul_of_nonneg_left (show d1 + n1 - min (2 * n1) (d1 - n1) + 1 ≤ n1 * z1 - d1 * z2 by omega) (by omega : (0 : ℤ) ≤ d2)]

set_option maxHeartbeats 400000 in
/-- Odd parity: `t_p(z) ≤ d₁`. -/
theorem gp_odd (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2)
    (he : n1 * d2 - n2 * d1 = -1)
    (hq : n2 ≤ n2 * z1 - d2 * z2) (hbox : -1 ≤ z2)
    (q3 : min (d2 - n2) (3 * n2 - d2) ≤ (d2 + n2) * z1 + (d2 - n2) * z2) (q2 : n2 * z1 - d2 * z2 ≤ d2) :
    n1 * z1 - d1 * z2 ≤ d1 := by
  have hz : 0 < z1 := by
    by_contra hc
    push Not at hc
    have hz2 : z2 ≤ -1 := by nlinarith
    have hz2' : z2 = -1 := by omega
    subst hz2'
    rcases min_choice (d2 - n2) (3 * n2 - d2) with hm | hm <;> rw [hm] at q3 <;> nlinarith
  have htr : d1 * (n2 * z1 - d2 * z2) = d2 * (n1 * z1 - d1 * z2) + z1 := by linear_combination (-z1) * he
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_left q2 (by omega : (0 : ℤ) ≤ d1),
    mul_le_mul_of_nonneg_left (show d1 + 1 ≤ n1 * z1 - d1 * z2 by omega) (by omega : (0 : ℤ) ≤ d2)]

end FLatticePaper.Tiles.AltLatticeOddWArith
