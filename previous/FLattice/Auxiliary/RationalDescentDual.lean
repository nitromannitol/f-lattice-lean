import FLattice.Auxiliary.RationalDescentData

/-! The exact gcd-normalized dual and its source lexicographic descent. -/

set_option autoImplicit false

namespace FLattice.Auxiliary.RationalDescent

/-- Literal normalization divisor of the dual parameter. -/
def dualDivisor (p : Pair) : ℕ := Nat.gcd (p.d-p.n) (p.d+p.n)

theorem dualDivisor_pos (p : Pair) : 0 < dualDivisor p := by
  apply Nat.gcd_pos_of_pos_right
  have h := p.d_pos
  omega

/-- The actual reduced dual pair, with all primitive-pair facts proved. -/
def dual (p : Pair) : Pair where
  n := (p.d-p.n)/dualDivisor p
  d := (p.d+p.n)/dualDivisor p
  d_pos := Nat.div_pos_iff.mpr ⟨dualDivisor_pos p,
    Nat.gcd_le_right _ (by have h := p.d_pos; omega)⟩
  n_le_d := Nat.div_le_div_right (by omega)
  coprime := Nat.coprime_div_gcd_div_gcd (dualDivisor_pos p)

/-- Exact recovery of the dual numerator before reduction. -/
theorem dual_scale_n (p : Pair) : dualDivisor p * (dual p).n = p.d-p.n :=
  Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _)

/-- Exact recovery of the dual denominator before reduction. -/
theorem dual_scale_d (p : Pair) : dualDivisor p * (dual p).d = p.d+p.n :=
  Nat.mul_div_cancel_left' (Nat.gcd_dvd_right _ _)

/-- Divisor two occurs precisely in the same-parity source case. -/
theorem dualDivisor_eq_two_iff (p : Pair) :
    dualDivisor p = 2 ↔ (p.n+p.d)%2=0 := by
  have hnd := p.n_le_d
  constructor
  · intro h
    have hd := Nat.gcd_dvd_right (p.d-p.n) (p.d+p.n)
    change dualDivisor p ∣ p.d+p.n at hd
    rw [h, Nat.dvd_iff_mod_eq_zero] at hd
    omega
  · intro h
    have hLeft : 2 ∣ p.d-p.n := Nat.dvd_of_mod_eq_zero (by omega)
    have hRight : 2 ∣ p.d+p.n := Nat.dvd_of_mod_eq_zero (by omega)
    have hb : 2 ∣ dualDivisor p := Nat.dvd_gcd hLeft hRight
    rcases dual_gcd_cases p with h1 | h2
    · change dualDivisor p = 1 at h1
      rw [h1] at hb
      omega
    · exact h2

/-- The product bκ is exactly two. -/
theorem dualDivisor_mul_kappa (p : Pair) : dualDivisor p * kappa p.n p.d = 2 := by
  rcases dual_gcd_cases p with h1 | h2
  · change dualDivisor p = 1 at h1
    have hOdd : (p.n+p.d)%2 ≠ 0 := by
      intro h
      have h2 := (dualDivisor_eq_two_iff p).mpr h
      omega
    simp [kappa, hOdd, h1]
  · change dualDivisor p = 2 at h2
    simp [kappa, (dualDivisor_eq_two_iff p).mp h2, h2]

/-- The reduced dual parity factor is exactly the normalizing divisor. -/
theorem dual_kappa (p : Pair) : kappa (dual p).n (dual p).d = dualDivisor p := by
  have hn := dual_scale_n p
  have hd := dual_scale_d p
  have hnd := p.n_le_d
  rcases dual_gcd_cases p with h1 | h2
  · change dualDivisor p = 1 at h1
    rw [h1] at hn hd
    have hEven : ((dual p).n+(dual p).d)%2=0 := by omega
    simp [kappa, hEven, h1]
  · change dualDivisor p = 2 at h2
    rw [h2] at hn hd
    have hEven := (dualDivisor_eq_two_iff p).mp h2
    have hOddD : p.d%2 ≠ 0 := by
      intro hD
      have hN : p.n%2=0 := by omega
      exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2)
        (Nat.dvd_of_mod_eq_zero hN) (Nat.dvd_of_mod_eq_zero hD) p.coprime
    have hOdd : ((dual p).n+(dual p).d)%2≠0 := by omega
    simp [kappa, hOdd, h2]

/-- The normalized dual has b²T'=2T, with no division identity assumed. -/
theorem dual_sizePolynomial (p : Pair) :
    (dualDivisor p)^2 * sizePolynomial (dual p).n (dual p).d =
      2 * sizePolynomial p.n p.d := by
  rw [← sizePolynomial_scale _ _ _ (dual p).n_le_d,
    dual_scale_n, dual_scale_d, sizePolynomial_dual _ _ p.n_le_d]

/-- Duality preserves the positive primary coordinate exactly. -/
theorem dual_primary (p : Pair) : primary (dual p) = primary p := by
  have hT := dual_sizePolynomial p
  have hK := dualDivisor_mul_kappa p
  unfold primary
  rw [dual_kappa]
  rcases dual_gcd_cases p with h1 | h2
  · change dualDivisor p = 1 at h1
    rw [h1] at hT hK ⊢
    nlinarith only [hT, hK]
  · change dualDivisor p = 2 at h2
    rw [h2] at hT hK ⊢
    nlinarith only [hT, hK]

/-- Above one half, the reduced dual ratio is strictly below one third. -/
theorem dual_below_third (p : Pair) (hHigh : p.d < 2*p.n) :
    3*(dual p).n < (dual p).d := by
  have hn := dual_scale_n p
  have hd := dual_scale_d p
  have hnd := p.n_le_d
  have hN : dualDivisor p * (dual p).n + p.n = p.d := by omega
  have hScaled : dualDivisor p * (3*(dual p).n) < dualDivisor p * (dual p).d := by
    nlinarith only [hN, hd, hHigh]
  exact Nat.lt_of_mul_lt_mul_left hScaled

/-- Duality lowers the source's secondary coordinate on the upper half. -/
theorem dual_secondary_lt (p : Pair) (hHigh : p.d < 2*p.n) :
    secondary (dual p) < secondary p := by
  have hLow := dual_below_third p hHigh
  have hNot : ¬ (dual p).d < 2*(dual p).n := by omega
  simp [secondary, hHigh, hNot]

end FLattice.Auxiliary.RationalDescent
