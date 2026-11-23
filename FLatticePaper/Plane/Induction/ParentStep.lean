import FLatticePaper.Plane.Induction.ChildFrame

/-! # The one-step identity of the parent field (task 49, inequality (2) of Q4-strips)

With `(p, q)` the odd parent of the earlier word, `ε = ±1`, and the shift `δ = (−ε(p + q), ε(p − q))`, the harmonic grid
satisfies the identity `ε(p(−x₂) − q(x₁ − 1)) + (h₀(x) − h₀(x + δ)) = −(T − ε(p + q))/2` with `T = q² + 2pq − p²`. This is the
harmonic part of `f(x) − f(x + δ) = P(Zx) − c₀` (the primitive price of the earlier field). -/

namespace FLatticePaper.Induction.ParentStep

/-- The numerator of the harmonic grid, `x₁² + 2x₁x₂ − x₂² − 2x₂ − (x₁ + x₂) mod 2`. -/
def numer (x1 x2 : ℤ) : ℤ := x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2

theorem harmonicGrid_eq_numer (x1 x2 : ℤ) : harmonicGrid (x1, x2) = numer x1 x2 / 4 := rfl

theorem numer_shift (p q ε x1 x2 : ℤ) (hε : ε = 1 ∨ ε = -1) :
    numer (x1 + -ε * (p + q)) (x2 + ε * (p - q)) =
      numer x1 x2 + 4 * (-ε * (q * x1 + p * x2) + (-p ^ 2 + 2 * p * q + q ^ 2 - ε * (p - q)) / 2) := by
  have hpar : (x1 + -ε * (p + q) + (x2 + ε * (p - q))) % 2 = (x1 + x2) % 2 := by
    have h : x1 + -ε * (p + q) + (x2 + ε * (p - q)) = (x1 + x2) + 2 * (-(ε * q)) := by ring
    rw [h, Int.add_mul_emod_self_left]
  have hM : (2 : ℤ) ∣ (-p ^ 2 + 2 * p * q + q ^ 2 - ε * (p - q)) := by
    rcases hε with rfl | rfl
    · have h1 : (2 : ℤ) ∣ q * (q + 1) := (Int.even_mul_succ_self q).two_dvd
      have h2 : (2 : ℤ) ∣ p * (p + 1) := (Int.even_mul_succ_self p).two_dvd
      have e : -p ^ 2 + 2 * p * q + q ^ 2 - 1 * (p - q) = 2 * (p * q) + q * (q + 1) - p * (p + 1) := by ring
      rw [e]
      exact dvd_sub (dvd_add (dvd_mul_right 2 _) h1) h2
    · have h1 : (2 : ℤ) ∣ q * (q - 1) := (Int.even_mul_pred_self q).two_dvd
      have h2 : (2 : ℤ) ∣ p * (p - 1) := (Int.even_mul_pred_self p).two_dvd
      have e : -p ^ 2 + 2 * p * q + q ^ 2 - -1 * (p - q) = 2 * (p * q) - p * (p - 1) + q * (q - 1) := by ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_right 2 _) h2) h1
  obtain ⟨k, hk⟩ := hM
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  unfold numer
  rw [hpar]
  rcases hε with rfl | rfl
  · linear_combination 2 * hk
  · linear_combination 2 * hk

/-- The harmonic part of the one-step identity of the parent field. -/
theorem parent_identity (p q ε x1 x2 : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ε * (p * (-x2) - q * (x1 - 1)) + (harmonicGrid (x1, x2) - harmonicGrid (x1 + -ε * (p + q), x2 + ε * (p - q))) =
      -((q * q + 2 * p * q - p * p - ε * (p + q)) / 2) := by
  have hM : (2 : ℤ) ∣ (-p ^ 2 + 2 * p * q + q ^ 2 - ε * (p - q)) := by
    rcases hε with rfl | rfl
    · have h1 : (2 : ℤ) ∣ q * (q + 1) := (Int.even_mul_succ_self q).two_dvd
      have h2 : (2 : ℤ) ∣ p * (p + 1) := (Int.even_mul_succ_self p).two_dvd
      have e : -p ^ 2 + 2 * p * q + q ^ 2 - 1 * (p - q) = 2 * (p * q) + q * (q + 1) - p * (p + 1) := by ring
      rw [e]
      exact dvd_sub (dvd_add (dvd_mul_right 2 _) h1) h2
    · have h1 : (2 : ℤ) ∣ q * (q - 1) := (Int.even_mul_pred_self q).two_dvd
      have h2 : (2 : ℤ) ∣ p * (p - 1) := (Int.even_mul_pred_self p).two_dvd
      have e : -p ^ 2 + 2 * p * q + q ^ 2 - -1 * (p - q) = 2 * (p * q) - p * (p - 1) + q * (q - 1) := by ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_right 2 _) h2) h1
  obtain ⟨k, hk⟩ := hM
  have hc : (q * q + 2 * p * q - p * p - ε * (p + q)) / 2 = k - ε * q := by
    have e : q * q + 2 * p * q - p * p - ε * (p + q) = 2 * (k - ε * q) := by
      rcases hε with rfl | rfl <;> linear_combination hk
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  have hshift : harmonicGrid (x1 + -ε * (p + q), x2 + ε * (p - q)) =
      harmonicGrid (x1, x2) + (-ε * (q * x1 + p * x2) + k) := by
    have hn := numer_shift p q ε x1 x2 hε
    have hk' : (-p ^ 2 + 2 * p * q + q ^ 2 - ε * (p - q)) / 2 = k := by
      rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    rw [hk'] at hn
    rw [harmonicGrid_eq_numer, harmonicGrid_eq_numer, hn, Int.add_mul_ediv_left _ _ (by norm_num : (4 : ℤ) ≠ 0)]
  rw [hshift, hc]
  ring

end FLatticePaper.Induction.ParentStep
