import FLatticePaper.Plane.Induction.Binary

/-! # The integer core of the lower input of an even free V root

For a child `n/d` (`0 < n < d`, `2 ≤ d - n`, `3 ≤ d`, coprime, `n` odd), with `P = d² + 2dn - n²` the period denominator,
an integer point `(a, b)` has `t = n a - d b` and `s = (d + n) a + (d - n) b`, and

* `P * a = (d - n) * t + d * s`,  `P * b = n * s - (d + n) * t`.

The lemmas below are the arithmetic of the even free V roots: `s ≤ 2n`, `d + n - P ≤ t ≤ 0`, and `s = 0` only at the origin,
`s = 2n` only at `vLast = (n - d + 1, n + d - 1)`. They are proved from the two identities, the polygon inequalities and a Bézout
witness `u n + v d = 1`, with no divisibility library. -/

namespace FLatticePaper.Induction.LowerBandCore

/-- No integer `k` with `P * k` strictly between `0` and `P`. -/
theorem no_mult_between {P V k : ℤ} (hP : 0 < P) (h0 : 0 < V) (h1 : V < P) (h : P * k = V) : False := by
  have hk1 : 0 < k := by
    by_contra hk
    push Not at hk
    nlinarith
  have hk2 : k < 1 := by
    by_contra hk
    push Not at hk
    nlinarith
  omega

/-- The branch `2n + 2 ≤ s` cannot carry a point with `t ≤ 2n - P - 1` (the lattice argument). -/
theorem no_far_branch {n d P a t s : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n) (hd3 : 3 ≤ d)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hcop : IsCoprime d (d - n))
    (hA : P * a = (d - n) * t + d * s)
    (ht1 : 2 - P ≤ t) (ht2 : t ≤ 2 * n - P - 1) (hs1 : 0 ≤ s) (hs2 : s ≤ d + n - 2) : False := by
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have key1 : P * (a + (d - n)) = (d - n) * (t + P) + d * s := by linear_combination hA
  have hV0 : 0 < (d - n) * (t + P) + d * s := by
    nlinarith [mul_nonneg (show (0:ℤ) ≤ d - n by omega) (show (0:ℤ) ≤ t + P - 2 by omega),
      mul_nonneg (show (0:ℤ) ≤ d by omega) hs1]
  have hk1 : 0 < a + (d - n) := by
    by_contra hk
    push Not at hk
    nlinarith [mul_nonneg hPpos.le (show (0:ℤ) ≤ -(a + (d - n)) by omega)]
  have hV1 : (d - n) * (t + P) + d * s < 2 * P := by
    nlinarith [mul_le_mul_of_nonneg_left (show t + P ≤ 2 * n - 1 by omega) (show (0:ℤ) ≤ d - n by omega),
      mul_le_mul_of_nonneg_left (show s ≤ d + n - 2 by omega) (show (0:ℤ) ≤ d by omega)]
  have hk2 : a + (d - n) < 2 := by
    by_contra hk
    push Not at hk
    nlinarith [mul_le_mul_of_nonneg_left hk hPpos.le]
  have ha : a = n - d + 1 := by omega
  have hA' : P * (n - d + 1) = (d - n) * t + d * s := by rw [ha] at hA; exact hA
  have key2 : d * (s - 2 * n) = -((d - n) * (t - (d + n - P))) := by
    linear_combination (-1 : ℤ) * hA' + hP
  have hdvd : d ∣ (d - n) * (t - (d + n - P)) := ⟨-(s - 2 * n), by linear_combination key2⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hkle : k ≤ -1 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (show (0:ℤ) ≤ d by omega) (show (0:ℤ) ≤ k by omega)]
  have hkge : -1 ≤ k := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show k ≤ -2 by omega) (show (0:ℤ) ≤ d by omega)]
  have hk' : k = -1 := by omega
  subst hk'
  have hw : t - (d + n - P) = -d := by linarith
  have h3 : d * (s - 2 * n) = d * (d - n) := by rw [hw] at key2; linear_combination key2
  have h4 : s - 2 * n = d - n := mul_left_cancel₀ (show d ≠ 0 by omega) h3
  omega

/-- The second branch of the V spectrum is at most `2n`: an even free V root has `s ≤ 2n`. -/
theorem core_s_le {n d P a t s : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n) (hd3 : 3 ≤ d)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hcop : IsCoprime d (d - n))
    (hA : P * a = (d - n) * t + d * s)
    (hpoly1 : 2 - P ≤ t) (hpoly3 : 0 ≤ s)
    (hsE : s % 2 = 0)
    (hspec : (0 ≤ s ∧ s ≤ 2 * n) ∨ (2 - d + n ≤ s ∧ s ≤ d + n - 2))
    (hnot : t < 2 * n - P ∨ s < 2 * n + 2) : s ≤ 2 * n := by
  by_contra h
  push Not at h
  have h2 : 2 * n + 2 ≤ s := by omega
  have hs2 : s ≤ d + n - 2 := by omega
  have ht : t ≤ 2 * n - P - 1 := by
    rcases hnot with h' | h'
    · omega
    · omega
  exact no_far_branch hn0 hnd hdn hd3 hP hcop hA hpoly1 ht hpoly3 hs2

/-- For `0 ≤ s ≤ 2n` the even free V root satisfies `d + n - P ≤ t ≤ 0`. -/
theorem core_t_bounds {n d P a t s : ℤ} (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n) (hd3 : 3 ≤ d)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2)
    (hA : P * a = (d - n) * t + d * s)
    (hpoly1 : 2 - P ≤ t) (hpoly2 : t ≤ d + n - 2) (hs1 : 0 ≤ s) (hs2 : s ≤ 2 * n) :
    d + n - P ≤ t ∧ t ≤ 0 := by
  have hPpos : 0 < P := by rw [hP]; nlinarith
  constructor
  · by_contra h
    push Not at h
    have key : P * (a + (d - n)) = (d - n) * (t + P) + d * s := by linear_combination hA
    refine no_mult_between hPpos ?_ ?_ key
    · nlinarith [mul_nonneg (show (0:ℤ) ≤ d - n by omega) (show (0:ℤ) ≤ t + P - 2 by omega),
        mul_nonneg (show (0:ℤ) ≤ d by omega) hs1]
    · nlinarith [mul_le_mul_of_nonneg_left (show t + P ≤ d + n - 1 by omega) (show (0:ℤ) ≤ d - n by omega),
        mul_le_mul_of_nonneg_left hs2 (show (0:ℤ) ≤ d by omega)]
  · by_contra h
    push Not at h
    refine no_mult_between hPpos ?_ ?_ hA
    · nlinarith [mul_nonneg (show (0:ℤ) ≤ d - n by omega) (show (0:ℤ) ≤ t - 1 by omega),
        mul_nonneg (show (0:ℤ) ≤ d by omega) hs1]
    · nlinarith [mul_le_mul_of_nonneg_left hpoly2 (show (0:ℤ) ≤ d - n by omega),
        mul_le_mul_of_nonneg_left hs2 (show (0:ℤ) ≤ d by omega)]

/-- At `s = 0` the even free V root is the origin `vFirst`. -/
theorem core_s0 {n d P a b t : ℤ} (hn0 : 0 < n) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (huv : ∃ u v : ℤ, u * n + v * d = 1) (hodd : n % 2 = 1)
    (hA : P * a = (d - n) * t + d * 0) (hB : P * b = n * 0 - (d + n) * t)
    (hEv : (a + b) % 2 = 0) (hlo : d + n - P ≤ t) (hhi : t ≤ 0) : a = 0 ∧ b = 0 := by
  obtain ⟨u, v, huv'⟩ := huv
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have h2d : 2 * d * t = P * (a - b) := by linear_combination (-1 : ℤ) * hA + hB
  have h2n : 2 * n * t = -(P * (a + b)) := by linear_combination hA + hB
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = v * (a - b) - u * (a + b) := ⟨_, rfl⟩
  have h2t : 2 * t = P * J := by
    rw [hJ]; linear_combination (-2 * t) * huv' + u * h2n + v * h2d
  have hJ1 : J ≤ 0 := by
    by_contra h
    push Not at h
    have : P * 1 ≤ P * J := mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ J by omega) hPpos.le
    omega
  have hJ2 : -1 ≤ J := by
    by_contra h
    push Not at h
    have : P * J ≤ P * (-2) := mul_le_mul_of_nonneg_left (show J ≤ -2 by omega) hPpos.le
    have hdn0 : 0 < d + n := by omega
    omega
  rcases (show J = 0 ∨ J = -1 by omega) with hJ0 | hJm
  · rw [hJ0, mul_zero] at h2t
    have ht0 : t = 0 := by omega
    have hPa : P * a = 0 := by rw [hA, ht0]; ring
    have hPb : P * b = 0 := by rw [hB, ht0]; ring
    exact ⟨(mul_eq_zero.mp hPa).resolve_left hPpos.ne', (mul_eq_zero.mp hPb).resolve_left hPpos.ne'⟩
  · rw [hJm] at h2t
    have hK : 2 * t = -P := by linear_combination h2t
    have h2a : P * (2 * a + (d - n)) = 0 := by linear_combination 2 * hA + (d - n) * hK
    have h2b : P * (2 * b - (d + n)) = 0 := by linear_combination 2 * hB - (d + n) * hK
    have ha2 : 2 * a + (d - n) = 0 := (mul_eq_zero.mp h2a).resolve_left hPpos.ne'
    have hb2 : 2 * b - (d + n) = 0 := (mul_eq_zero.mp h2b).resolve_left hPpos.ne'
    omega

/-- At `s = 2n` the even free V root is `vLast = (n - d + 1, n + d - 1)`. -/
theorem core_s2n {n d P a b t : ℤ} (hn0 : 0 < n) (hdn : 2 ≤ d - n)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (huv : ∃ u v : ℤ, u * n + v * d = 1) (hodd : n % 2 = 1)
    (hA : P * a = (d - n) * t + d * (2 * n)) (hB : P * b = n * (2 * n) - (d + n) * t)
    (hEv : (a + b) % 2 = 0) (hlo : d + n - P ≤ t) (hhi : t ≤ 0) :
    a = n - d + 1 ∧ b = n + d - 1 := by
  obtain ⟨u, v, huv'⟩ := huv
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hα : P * (a - (n - d + 1)) = (d - n) * (t - (d + n - P)) := by linear_combination hA - hP
  have hβ : P * (b - (n + d - 1)) = -(d + n) * (t - (d + n - P)) := by linear_combination hB + hP
  obtain ⟨α, hαd⟩ : ∃ α : ℤ, α = a - (n - d + 1) := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ, β = b - (n + d - 1) := ⟨_, rfl⟩
  obtain ⟨τ, hτd⟩ : ∃ τ : ℤ, τ = t - (d + n - P) := ⟨_, rfl⟩
  rw [← hαd, ← hτd] at hα
  rw [← hβd, ← hτd] at hβ
  have h2d : 2 * d * τ = P * (α - β) := by linear_combination (-1 : ℤ) * hα + hβ
  have h2n : 2 * n * τ = -(P * (α + β)) := by linear_combination hα + hβ
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = v * (α - β) - u * (α + β) := ⟨_, rfl⟩
  have h2t : 2 * τ = P * J := by
    rw [hJ]; linear_combination (-2 * τ) * huv' + u * h2n + v * h2d
  have hτ0 : 0 ≤ τ := by omega
  have hτ1 : τ ≤ P - (d + n) := by omega
  have hJ1 : J ≤ 1 := by
    by_contra h
    push Not at h
    have : P * 2 ≤ P * J := mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ J by omega) hPpos.le
    have hdn0 : 0 < d + n := by omega
    omega
  have hJ2 : 0 ≤ J := by
    by_contra h
    push Not at h
    have : P * J ≤ P * (-1) := mul_le_mul_of_nonneg_left (show J ≤ -1 by omega) hPpos.le
    omega
  rcases (show J = 0 ∨ J = 1 by omega) with hJ0 | hJ1'
  · rw [hJ0, mul_zero] at h2t
    have hτ' : τ = 0 := by omega
    have hPα : P * α = 0 := by rw [hα, hτ']; ring
    have hPβ : P * β = 0 := by rw [hβ, hτ']; ring
    have hα0 : α = 0 := (mul_eq_zero.mp hPα).resolve_left hPpos.ne'
    have hβ0 : β = 0 := (mul_eq_zero.mp hPβ).resolve_left hPpos.ne'
    omega
  · rw [hJ1'] at h2t
    have hK : 2 * τ = P := by linear_combination h2t
    have h2α : P * (2 * α - (d - n)) = 0 := by linear_combination 2 * hα + (d - n) * hK
    have h2β : P * (2 * β + (d + n)) = 0 := by linear_combination 2 * hβ - (d + n) * hK
    have hα2 : 2 * α - (d - n) = 0 := (mul_eq_zero.mp h2α).resolve_left hPpos.ne'
    have hβ2 : 2 * β + (d + n) = 0 := (mul_eq_zero.mp h2β).resolve_left hPpos.ne'
    omega

end FLatticePaper.Induction.LowerBandCore
