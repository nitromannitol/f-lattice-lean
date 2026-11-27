import Mathlib

/-! Pure arithmetic of the cone boundary (grades t x = n*x1 - d*x2, s x = (d+n)*x1 + (d-n)*x2, T = d*d + 2*d*n - n*n).
Grades: t x = n*x1 - d*x2, s x = (d+n)*x1 + (d-n)*x2, T = d*d + 2*d*n - n*n. -/

namespace FLatticePaper.ConeFaceArith

theorem T_even {n d T : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) :
    ∃ τ, T = 2*τ := by
  obtain ⟨a, ha⟩ : ∃ a, n = 2*a+1 := ⟨n/2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, d = 2*b+1 := ⟨d/2, by omega⟩
  exact ⟨2*b^2+4*b+4*a*b-2*a^2+1, by rw [hT, ha, hb]; ring⟩

theorem s_par {n d x1 x2 : ℤ} (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) :
    ∃ k, (d+n)*x1 + (d-n)*x2 = 2*k := by
  obtain ⟨m, hm⟩ : ∃ m, d + n = 2*m := ⟨(d+n)/2, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, d - n = 2*e := ⟨(d-n)/2, by omega⟩
  exact ⟨m*x1 + e*x2, by rw [hm, he]; ring⟩

theorem t_par_even {n d x1 x2 : ℤ} (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) (hx : (x1 + x2) % 2 = 0) :
    ∃ k, n*x1 - d*x2 = 2*k := by
  obtain ⟨a, ha⟩ : ∃ a, n = 2*a+1 := ⟨n/2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, d = 2*b+1 := ⟨d/2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, x1 + x2 = 2*c := ⟨(x1+x2)/2, by omega⟩
  exact ⟨a*x1 - b*x2 - x2 + c, by rw [ha, hb]; linear_combination hc⟩

theorem base_s {n d T z1 z2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hz1 : 2 ≤ z1) (hzt2 : n*z1 - d*z2 ≤ d - 2) :
    d + 3*n - 2 < (d+n)*z1 + (d-n)*z2 := by
  have hd : 0 < d := by linarith
  have key : d * ((d+n)*z1 + (d-n)*z2) = T*z1 - (d-n)*(n*z1 - d*z2) := by rw [hT]; ring
  have hT0 : 0 ≤ T := by
    rw [hT]; nlinarith [mul_le_mul_of_nonneg_right hnd (show (0:ℤ) ≤ n by linarith)]
  have h1 : 2*T ≤ T*z1 := by nlinarith [mul_le_mul_of_nonneg_left hz1 hT0]
  have h2 : (d-n)*(n*z1 - d*z2) ≤ (d-n)*(d-2) := mul_le_mul_of_nonneg_left hzt2 (by linarith)
  have h3 : d*(d+3*n-2) < d*((d+n)*z1 + (d-n)*z2) := by
    rw [key]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ n by linarith) (show (0:ℤ) ≤ d-n by linarith)]
  exact lt_of_mul_lt_mul_left h3 hd.le

theorem cone_s_odd {n d z1 z2 x1 x2 : ℤ} (hL : 0 ≤ d+n) (ha : x2 - z2 ≤ x1 - z1) :
    (d+n)*z1 + (d-n)*z2 + 2*d*(x2-z2) ≤ (d+n)*x1 + (d-n)*x2 := by
  nlinarith [mul_le_mul_of_nonneg_left ha hL]

theorem cone_s_even {n d z1 z2 x1 x2 : ℤ} (hL : 0 ≤ d+n) (ha : x2 - z2 - 1 ≤ x1 - z1) :
    (d+n)*z1 + (d-n)*z2 + 2*d*(x2-z2) - (d+n) ≤ (d+n)*x1 + (d-n)*x2 := by
  nlinarith [mul_le_mul_of_nonneg_left ha hL]

theorem cone_t_odd {n d z1 z2 x1 x2 : ℤ} (hn0 : 0 ≤ n) (ha : x2 - z2 ≤ x1 - z1) :
    n*z1 - d*z2 + (n-d)*(x2-z2) ≤ n*x1 - d*x2 := by
  nlinarith [mul_le_mul_of_nonneg_left ha hn0]

theorem cone_t_even {n d z1 z2 x1 x2 : ℤ} (hn0 : 0 ≤ n) (ha : x2 - z2 - 1 ≤ x1 - z1) :
    n*z1 - d*z2 + (n-d)*(x2-z2) - n ≤ n*x1 - d*x2 := by
  nlinarith [mul_le_mul_of_nonneg_left ha hn0]

theorem parity_top (S T d n k τ : ℤ) (hS : S = 2*k) (hτ : T = 2*τ) (hn2 : n % 2 = 1) (hd2 : d % 2 = 1)
    (h1 : T - d + n ≤ S) (h2 : S < T + 2 - d + n) : S = T - d + n := by
  omega

theorem odd_s_ne_top {n d T x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) (hcop : IsCoprime n d) (hxo : (x1 + x2) % 2 = 1)
    (ht1 : d - T < n*x1 - d*x2) (ht2 : n*x1 - d*x2 < n)
    (hs : (d+n)*x1 + (d-n)*x2 = T - d + n) : False := by
  obtain ⟨e, he⟩ : ∃ e, d - n = 2*e := ⟨(d-n)/2, by omega⟩
  have he1 : 1 ≤ e := by omega
  have hdn : d = n + 2*e := by omega
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have htau : T = 2*(n^2 + e*(4*n+2*e)) := by rw [hT, hdn]; ring
  have hdpos : 0 < d - n := by omega
  have hid : T*(x1 - d) = (d-n)*(n*x1 - d*x2 - d) := by linear_combination d * hs + x1 * hT
  have hid2 : (n^2 + e*(4*n+2*e))*(x1 - d) = e*(n*x1 - d*x2 - d) := by
    have h2 : 2*((n^2 + e*(4*n+2*e))*(x1 - d)) = 2*(e*(n*x1 - d*x2 - d)) := by
      rw [htau, he] at hid; linear_combination hid
    linarith
  have hcopn : IsCoprime n (2*e) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u + v, v, by rw [hdn] at huv; linear_combination huv⟩
  have hcopn' : IsCoprime n e := hcopn.of_mul_right_right
  have hpow : IsCoprime e (n^2) := hcopn'.symm.pow_right
  have hcopτ : IsCoprime e (n^2 + e*(4*n+2*e)) := hpow.add_mul_left_right (4*n+2*e)
  have hdvd : e ∣ x1 - d := hcopτ.dvd_of_dvd_mul_left ⟨n*x1 - d*x2 - d, hid2⟩
  obtain ⟨k, hk⟩ := hdvd
  have hx1n : n < x1 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hdpos (show 0 < n*x1 - d*x2 - d + T by linarith),
      mul_nonneg hT0.le (show 0 ≤ n - x1 by linarith)]
  have hx1d : x1 < d := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hdpos (show 0 < (n - d) - (n*x1 - d*x2 - d) by linarith),
      mul_nonneg hT0.le (show 0 ≤ x1 - d by linarith), mul_pos hdpos hdpos]
  have hpos : 0 < e := by omega
  have hk1 : k = -1 := by
    have hA : e*k < 0 := by linarith
    have hB : -2*e < e*k := by linarith
    have hk_neg : k < 0 := by
      by_contra h; push Not at h; nlinarith [mul_nonneg hpos.le h]
    have hk_gt : -2 < k := by
      by_contra h; push Not at h; nlinarith [mul_le_mul_of_nonneg_left h hpos.le]
    omega
  have hx1 : x1 = n + e := by rw [hk1] at hk; linarith
  have h2e : 2*e*(x2 - (2*n + e - 1)) = 0 := by
    have hs' := hs
    rw [hdn, htau, hx1] at hs'
    linear_combination hs'
  have hx2 : x2 = 2*n + e - 1 := by
    have hne : 2*e ≠ 0 := by omega
    have := (mul_eq_zero.mp h2e).resolve_left hne
    linarith
  rw [hx1, hx2] at hxo
  omega

theorem even_t_zero {n d T x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hcop : IsCoprime n d) (ht : n*x1 - d*x2 = 0) (hs1 : 2*n < (d+n)*x1 + (d-n)*x2)
    (hs2 : (d+n)*x1 + (d-n)*x2 < T) : False := by
  have hd0 : d ≠ 0 := by omega
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hdvd : d ∣ x1 := by
    have h1 : d ∣ x1 * n := ⟨x2, by linear_combination ht⟩
    exact (IsCoprime.symm hcop).dvd_of_dvd_mul_right h1
  obtain ⟨k, rfl⟩ := hdvd
  have hx2 : x2 = n*k := by
    have h : d*x2 = d*(n*k) := by linear_combination -ht
    exact mul_left_cancel₀ hd0 h
  subst x2
  have hsk : (d+n)*(d*k) + (d-n)*(n*k) = k*T := by rw [hT]; ring
  rw [hsk] at hs1 hs2
  have hk1 : 0 < k := by
    by_contra h; push Not at h; nlinarith
  have hk2 : k < 1 := by
    by_contra h; push Not at h; nlinarith
  omega

theorem even_s_high {n d z1 z2 x1 x2 : ℤ} (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hsz : d + 3*n - 2 < (d+n)*z1 + (d-n)*z2)
    (hh : 1 ≤ x2 - z2) (ha : x2 - z2 - 1 ≤ x1 - z1) :
    2*(d+n) - 2 < (d+n)*x1 + (d-n)*x2 := by
  have hcs := cone_s_even (d := d) (show (0:ℤ) ≤ d+n by linarith) ha
  nlinarith [mul_le_mul_of_nonneg_left hh (show (0:ℤ) ≤ 2*d by linarith)]

theorem even_t_low {n d T z1 z2 x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hzt1 : n + 2 ≤ n*z1 - d*z2) (hsz : d + 3*n - 2 < (d+n)*z1 + (d-n)*z2)
    (hh : 1 ≤ x2 - z2) (ha : x2 - z2 - 1 ≤ x1 - z1) (hsx : (d+n)*x1 + (d-n)*x2 < T) :
    (d+n) - T < n*x1 - d*x2 := by
  have hL : (0:ℤ) ≤ d + n := by linarith
  have hcs := cone_s_even (d := d) hL ha
  have hct := cone_t_even (d := d) (show (0:ℤ) ≤ n by linarith) ha
  have h2dh : 2*d*(x2-z2) < T - 2*n + 2 := by linarith
  have hdpos : 0 < d - n := by linarith
  have key : (d-n)*(x2-z2) < T - d - n + 2 := by
    have hA : (d-n)*(2*d*(x2-z2)) < (d-n)*(T - 2*n + 2) := mul_lt_mul_of_pos_left h2dh hdpos
    have hB : (d-n)*(T - 2*n + 2) ≤ 2*d*(T - d - n + 2) := by
      rw [hT]
      nlinarith [mul_nonneg (show (0:ℤ) ≤ d - 2*n by linarith) (mul_self_nonneg d),
        mul_nonneg (mul_self_nonneg n) (show (0:ℤ) ≤ d - n by linarith),
        mul_nonneg (show (0:ℤ) ≤ n by linarith) (mul_self_nonneg d)]
    have hC : 2*d*((d-n)*(x2-z2)) < 2*d*(T - d - n + 2) := by nlinarith
    exact lt_of_mul_lt_mul_left hC (by linarith)
  linarith

/-- Input `x + (1,0)` of an even open point: its odd openness holds except the top `s`-face. -/
theorem face_even_pos {n d T x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) (hcop : IsCoprime n d) (hx : (x1 + x2) % 2 = 0)
    (he_t1 : d+n-2-T < n*x1 - d*x2) (he_t2 : n*x1 - d*x2 < 2)
    (he_s1 : 2*n < (d+n)*x1 + (d-n)*x2) (he_s2 : (d+n)*x1 + (d-n)*x2 < T) :
    d - T < n*(x1+1) - d*x2 ∧ n*(x1+1) - d*x2 < n ∧ d+n-2 < (d+n)*(x1+1) + (d-n)*x2 := by
  obtain ⟨k, hk⟩ := t_par_even hn2 hd2 hx
  have hne : n*x1 - d*x2 ≠ 0 := fun h => even_t_zero hT hn hnd hcop h he_s1 he_s2
  have ht_le : n*x1 - d*x2 ≤ -2 := by
    generalize n*x1 - d*x2 = t at *
    omega
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Input `x - (1,0)` of an even cone point: always odd-open. -/
theorem face_even_neg {n d T z1 z2 x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hzt1 : n + 2 ≤ n*z1 - d*z2) (hsz : d + 3*n - 2 < (d+n)*z1 + (d-n)*z2)
    (hh : 1 ≤ x2 - z2) (ha : x2 - z2 - 1 ≤ x1 - z1)
    (hsx : (d+n)*x1 + (d-n)*x2 < T) (he_t2 : n*x1 - d*x2 < 2) :
    d - T < n*(x1-1) - d*x2 ∧ n*(x1-1) - d*x2 < n ∧ d+n-2 < (d+n)*(x1-1) + (d-n)*x2 ∧
      (d+n)*(x1-1) + (d-n)*x2 < T + 2 - d + n := by
  have E3 := even_t_low hT hn hnd hzt1 hsz hh ha hsx
  have E4 := even_s_high hn hnd hsz hh ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- Input `x - (0,1)` of an odd cone point (even, `t` grows by `d`): all three open conditions. -/
theorem face_odd_neg {n d T z1 z2 x1 x2 : ℤ} (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hsz : d + 3*n - 2 < (d+n)*z1 + (d-n)*z2) (hh : 1 ≤ x2 - z2) (ha : x2 - z2 ≤ x1 - z1)
    (hO1 : d - T < n*x1 - d*x2) (hO4 : (d+n)*x1 + (d-n)*x2 < T + 2 - d + n) :
    d+n-2-T < n*x1 - d*(x2-1) ∧ 2*n < (d+n)*x1 + (d-n)*(x2-1) ∧
      (d+n)*x1 + (d-n)*(x2-1) < T := by
  have hL : (0:ℤ) ≤ d+n := by linarith
  have hcs := cone_s_odd (d := d) hL ha
  have h2 : 2*d ≤ 2*d*(x2-z2) := by
    nlinarith [mul_le_mul_of_nonneg_left hh (show (0:ℤ) ≤ 2*d by linarith)]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Input `x + (0,1)` of an odd cone point (even, `t` drops by `d`): all three open conditions. -/
theorem face_odd_pos {n d T z1 z2 x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n)
    (hnd : 2*n ≤ d) (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) (hcop : IsCoprime n d)
    (hzt1 : n + 2 ≤ n*z1 - d*z2) (hsz : d + 3*n - 2 < (d+n)*z1 + (d-n)*z2)
    (hh : 1 ≤ x2 - z2) (ha : x2 - z2 ≤ x1 - z1) (hxo : (x1 + x2) % 2 = 1)
    (hO1 : d - T < n*x1 - d*x2) (hO2 : n*x1 - d*x2 < n)
    (hO3 : d+n-2 < (d+n)*x1 + (d-n)*x2) (hO4 : (d+n)*x1 + (d-n)*x2 < T + 2 - d + n) :
    d+n-2-T < n*x1 - d*(x2+1) ∧ 2*n < (d+n)*x1 + (d-n)*(x2+1) ∧
      (d+n)*x1 + (d-n)*(x2+1) < T := by
  have hL : (0:ℤ) ≤ d+n := by linarith
  have hdpos : 0 < d - n := by linarith
  have hsne : (d+n)*x1 + (d-n)*x2 < T - d + n := by
    obtain ⟨k, hk⟩ := s_par (x1 := x1) (x2 := x2) hn2 hd2
    obtain ⟨τ, hτ⟩ := T_even hT hn2 hd2
    by_contra hc
    push Not at hc
    have heq := parity_top _ T d n k τ hk hτ hn2 hd2 hc hO4
    exact odd_s_ne_top hT hn hnd hn2 hd2 hcop hxo hO1 hO2 heq
  have hE8 : d+n-2-T < n*x1 - d*(x2+1) := by
    by_contra hc
    push Not at hc
    have hc1 := cone_t_odd (d := d) (show (0:ℤ) ≤ n by linarith) ha
    have hc2 := cone_s_odd (d := d) hL ha
    have A : T - 2*d + 4 ≤ (d-n)*(x2-z2) := by nlinarith
    have B : 2*d*(x2-z2) < T - 2*d - 2*n + 2 := by linarith
    have C : (d-n)*(2*d*(x2-z2)) < (d-n)*(T-2*d-2*n+2) := mul_lt_mul_of_pos_left B hdpos
    have D : 2*d*(T-2*d+4) ≤ 2*d*((d-n)*(x2-z2)) :=
      mul_le_mul_of_nonneg_left A (by linarith)
    have E : (d-n)*(T-2*d-2*n+2) ≤ 2*d*(T-2*d+4) := by
      rw [hT]
      nlinarith [mul_nonneg (mul_self_nonneg d) (show (0:ℤ) ≤ d - 2 by linarith),
        mul_nonneg (mul_self_nonneg n) (show (0:ℤ) ≤ d - n by linarith),
        mul_nonneg (mul_self_nonneg d) (show (0:ℤ) ≤ n by linarith),
        mul_nonneg (show (0:ℤ) ≤ n by linarith) (show (0:ℤ) ≤ d - n by linarith)]
    linarith
  refine ⟨hE8, ?_, ?_⟩
  · linarith
  · linarith

/-- Lower bound of the V index: an even open point whose right input is a V-face point has `x2 > n`. -/
theorem V_low_arith {n d T x1 x2 : ℤ} (hT : T = d*d + 2*d*n - n*n) (hn : 1 ≤ n) (hnd : 2*n ≤ d)
    (hn2 : n % 2 = 1) (hd2 : d % 2 = 1) (hxe : (x1 + x2) % 2 = 0)
    (ht0 : n*x1 - d*x2 ≤ 0) (hO4 : (d+n)*x1 + (d-n)*x2 < T)
    (hV : T + 2 - d + n ≤ (d+n)*(x1+1) + (d-n)*x2) (hk : x2 ≤ n) : False := by
  have hL : (0:ℤ) < d + n := by linarith
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hA : n*((d+n)*x1 + (d-n)*x2) ≤ T*x2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht0 hL.le]
  have hB : n*(T + 2 - 2*d) ≤ T*x2 := by
    nlinarith [mul_le_mul_of_nonneg_left (show T + 2 - 2*d ≤ (d+n)*x1 + (d-n)*x2 by linarith) (show (0:ℤ) ≤ n by linarith)]
  have hC : n ≤ x2 := by
    by_contra hc
    push Not at hc
    have h1 : x2 ≤ n - 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h1 hT0.le]
  have hx2 : x2 = n := le_antisymm hk hC
  subst x2
  have hx1d : x1 ≤ d - 1 := by
    have h1 := hO4
    rw [hT] at h1
    by_contra hc
    push Not at hc
    nlinarith
  have hx1e : d - 1 ≤ x1 := by
    by_contra hc
    push Not at hc
    have h2 : x1 ≤ d - 2 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h2 hL.le]
  have hx1 : x1 = d - 1 := le_antisymm hx1d hx1e
  subst x1
  omega

/-- The product `n * r` for the odd parent `r = D + N` with `N ≥ 1` and `N d − D n = e ≤ 1`. -/
theorem nr_ge_arith {n d D N e : ℤ} (heps : e = N*d - D*n) (he1 : e ≤ 1) (hN : 1 ≤ N) (hL : 0 ≤ d + n) :
    d + n - 1 ≤ n*(D+N) := by
  nlinarith [mul_le_mul_of_nonneg_right hN hL]

/-- Upper bound of the V index: `x2 − n ≤ r` from `z2 ≤ n − 1`, `x2 ≤ z2 + K − 1`, `n K ≤ d + 3n − 2`, `n r ≥ d + n − 1`. -/
theorem V_up_arith {n d K z2 x2 r : ℤ} (hn : 1 ≤ n) (hz2 : z2 ≤ n - 1) (hx2 : x2 ≤ z2 + K - 1)
    (hK : n*K ≤ d + 3*n - 2) (hr : d + n - 1 ≤ n*r) : x2 - n ≤ r := by
  by_contra hc
  push Not at hc
  have h1 : x2 - n ≤ K - 2 := by omega
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0:ℤ) ≤ n by linarith),
    mul_le_mul_of_nonneg_left (show r + 1 ≤ x2 - n by omega) (show (0:ℤ) ≤ n by linarith)]

end FLatticePaper.ConeFaceArith
