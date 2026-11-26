import FLatticePaper.Plane.Induction.VLattice

/-! # Grade bounds of the odd free V roots, from the lattice identity `T z₂ = n s − (d+n) t`

For an odd site with closed grades `n − T ≤ t ≤ d` and `2 − d + n ≤ s ≤ d + n − 2`, the identity `T z₂ = n s − (d+n) t` confines `z₂` to
`{0, 1}`, and both cases contradict `t ≥ 2 − n`. So `t ≤ 1 − n`. This is the bound that makes `z + (1,0)` strictly interior for the
`η = +1` source of the `v3` last arrow. -/

namespace FLatticePaper.VGradeBounds

theorem t_le_one_sub_n {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hodd : (z1 + z2) % 2 = 1)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (hthi : t ≤ d)
    (hslo : 2 - d + n ≤ s) (hshi : s ≤ d + n - 2) : t ≤ 1 - n := by
  by_contra hc
  push Not at hc
  have hTpos : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hV : (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * s - (d + n) * t := by
    rw [ht, hs]; ring
  have hn0 : (0:ℤ) ≤ n := by omega
  have hdn0 : (0:ℤ) ≤ d + n := by omega
  -- lower bound: T z₂ ≥ −T + 2n
  have hlow : -(d ^ 2 + 2 * d * n - n ^ 2) + 2 * n ≤ (d ^ 2 + 2 * d * n - n ^ 2) * z2 := by
    rw [hV]
    nlinarith [mul_le_mul_of_nonneg_left hslo hn0, mul_le_mul_of_nonneg_left hthi hdn0]
  -- upper bound: T z₂ ≤ n(d+n−2) − (d+n)(2−n)
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * z2 ≤ n * (d + n - 2) - (d + n) * (2 - n) := by
    rw [hV]
    nlinarith [mul_le_mul_of_nonneg_left hshi hn0, mul_le_mul_of_nonneg_left hc hdn0]
  have hz2a : 0 ≤ z2 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show z2 ≤ -1 by omega) hTpos.le]
  have hz2b : z2 ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ z2 by omega) hTpos.le]
  rcases (show z2 = 0 ∨ z2 = 1 by omega) with h0 | h1
  · subst h0
    have hz1 : z1 = 0 := by
      rcases (show z1 ≤ -1 ∨ z1 = 0 ∨ 1 ≤ z1 by omega) with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    subst hz1
    omega
  · subst h1
    have hz1 : z1 ≤ 0 := by
      by_contra h
      push Not at h
      nlinarith
    have hpos : 0 < n * z1 := by nlinarith
    nlinarith

/-- **The lower bound on `t` for the odd free V roots**: `t ≥ n + 2d − T` (sharp at `z = (n−d+1, d+n−2)`). The lattice identity
`T (z₂ − (d+n)) = n s − (d+n)(t+T)` with `t + T ≤ n + 2d − 1` leaves `z₂ − (d+n) ∈ {−1, −2}`; the value `−2` forces
`t + T = 2d` and contradicts the lower `s` bound, and `−1` forces `t + T = d + n` (by `n ∣ d(t+T−d)`), which is even, contradicting
the oddness of `z`. -/
theorem t_ge_n_add_two_d_sub_T {n d z1 z2 t s : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hnO : n % 2 = 1) (hdO : d % 2 = 1)
    (hcop : IsCoprime n d) (hodd : (z1 + z2) % 2 = 1)
    (ht : t = n * z1 - d * z2) (hs : s = (d + n) * z1 + (d - n) * z2)
    (htlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t) (hthi : t ≤ d)
    (hslo : 2 - d + n ≤ s) (hshi : s ≤ d + n - 2) : n + 2 * d - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t := by
  by_contra hc
  push Not at hc
  obtain ⟨T, hTdef⟩ : ∃ T, T = d ^ 2 + 2 * d * n - n ^ 2 := ⟨_, rfl⟩
  rw [← hTdef] at htlo hc
  have hTpos : 0 < T := by rw [hTdef]; nlinarith
  have hn0 : (0:ℤ) ≤ n := by omega
  have hdn0 : (0:ℤ) ≤ d + n := by omega
  have hV : T * z2 = n * s - (d + n) * t := by rw [hTdef, ht, hs]; ring
  obtain ⟨U, hUdef⟩ : ∃ U, U = t + T := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, y = z2 - (d + n) := ⟨_, rfl⟩
  have hid : T * y = n * s - (d + n) * U := by rw [hydef, hUdef]; linear_combination hV
  have hU1 : n ≤ U := by rw [hUdef]; linarith
  have hU2 : U ≤ n + 2 * d - 1 := by rw [hUdef]; omega
  have hyup : T * y ≤ -2 * n := by
    nlinarith [mul_le_mul_of_nonneg_left hshi hn0, mul_le_mul_of_nonneg_left hU1 hdn0]
  have hylo : n * (2 - d + n) - (d + n) * (n + 2 * d - 1) ≤ T * y := by
    nlinarith [mul_le_mul_of_nonneg_left hslo hn0, mul_le_mul_of_nonneg_left hU2 hdn0]
  have hy1 : y ≤ -1 := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show (0:ℤ) ≤ y by omega) hTpos.le]
  have hy2 : -2 ≤ y := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left (show y ≤ -3 by omega) hTpos.le, hTdef]
  rcases (show y = -1 ∨ y = -2 by omega) with h1 | h2
  · -- `y = −1`: `n s = (d+n) U − T`, `n ∣ (U − d) d`, so `U = d + n`, `s = 2n`, `t = d + n − T` is even
    subst h1
    have hdiv : n ∣ (U - d) * d := ⟨s - U + 2 * d - n, by linear_combination hid + hTdef⟩
    obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_right hdiv
    have hUlo : d < U := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left h hdn0, mul_le_mul_of_nonneg_left hslo hn0]
    have hUhi : U < d + 2 * n := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left h hdn0, mul_le_mul_of_nonneg_left hshi hn0, mul_nonneg hn0 hn0]
    have hkpos : 0 < k := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left h hn0]
    have hklt : k < 2 := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left h hn0]
    have hk1 : k = 1 := by omega
    have hUd : U = d + n := by rw [hk1] at hk; linarith
    have hs2n : s = 2 * n := by
      have h1 : n * s = n * (2 * n) := by linear_combination (d + n) * hUd + (-1 : ℤ) * hTdef + (-1 : ℤ) * hid
      exact mul_left_cancel₀ (by omega) h1
    obtain ⟨a, rfl⟩ : ∃ a, d = 2 * a + 1 := ⟨d / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, n = 2 * b + 1 := ⟨n / 2, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, t = 2 * e + (z1 + z2) := ⟨b * z1 - (a + 1) * z2, by rw [ht]; ring⟩
    obtain ⟨f, hf⟩ : ∃ f, T = 2 * f :=
      ⟨2 * (a - b) * (a + b + 1) + (2 * a + 1) * (2 * b + 1), by rw [hTdef]; ring⟩
    have htq : t = U - T := by rw [hUdef]; ring
    have htq2 : t = 2 * (a + b + 1) - T := by rw [htq, hUd]; ring
    omega
  · -- `y = −2`: `n s = (d+n) U − 2T`, `n ∣ (U − 2d) d`, so `U = 2d`, then `s = 2(n − d)` contradicts the lower `s` bound
    subst h2
    have hdiv : n ∣ (U - 2 * d) * d := ⟨s - U + 4 * d - 2 * n, by linear_combination hid + 2 * hTdef⟩
    obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_right hdiv
    have hU3 : 2 * d - n < U := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left h hdn0, mul_le_mul_of_nonneg_left hslo hn0,
        mul_nonneg hn0 (show (0:ℤ) ≤ d by omega)]
    have hk0 : k ≤ 0 := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ k by omega) hn0]
    have hkge : 0 ≤ k := by
      by_contra h
      push Not at h
      linarith [mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) hn0]
    have hk0' : k = 0 := by omega
    have hU2d : U = 2 * d := by rw [hk0'] at hk; linarith
    have h3 : n * s = n * (2 * (n - d)) := by linear_combination (d + n) * hU2d + (-2 : ℤ) * hTdef + (-1 : ℤ) * hid
    have hs' : s = 2 * (n - d) := mul_left_cancel₀ (by omega) h3
    omega

end FLatticePaper.VGradeBounds
