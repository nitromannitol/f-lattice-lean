import FLatticePaper.Plane.Induction.VLattice

/-! # The even closed site with zero `s`-grade is the origin

For an even site `(x, y)` with `s = (d+n) x + (d−n) y = 0` and `t = n x − d y` in the closed range `2 − T ≤ t ≤ d + n − 2`, the
identities `T x = (d−n) t` and `T y = −(d+n) t` and a Bézout relation `a n + b d = 1` give `2 t = T k` with `k = (b−a) x − (a+b) y`.
The range forces `k ∈ {−1, 0, 1}`; `k = ±1` makes `x + y` odd, against the parity of the site, and `k = 0` gives `x = y = 0`. -/

namespace FLatticePaper.VZeroS

theorem origin_of_s_zero {n d x y : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hnO : n % 2 = 1) (hcop : IsCoprime n d)
    (hpar : (x + y) % 2 = 0) (hs0 : (d + n) * x + (d - n) * y = 0)
    (htlo : 2 - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * x - d * y)
    (hthi : n * x - d * y ≤ d + n - 2) : x = 0 ∧ y = 0 := by
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨T, hTdef⟩ : ∃ T, T = d ^ 2 + 2 * d * n - n ^ 2 := ⟨_, rfl⟩
  rw [← hTdef] at htlo
  have hTpos : 0 < T := by rw [hTdef]; nlinarith
  have hTbig : d + n - 2 < T := by rw [hTdef]; nlinarith
  obtain ⟨t, htdef⟩ : ∃ t, t = n * x - d * y := ⟨_, rfl⟩
  rw [← htdef] at htlo hthi
  have hTx : T * x = (d - n) * t := by
    rw [hTdef, htdef]; linear_combination (d) * hs0
  have hTy : T * y = -((d + n) * t) := by
    rw [hTdef, htdef]; linear_combination (n) * hs0
  -- `2 t = T k` with `k = (b − a) x − (a + b) y`
  obtain ⟨k, hk⟩ : ∃ k, k = (b - a) * x - (a + b) * y := ⟨_, rfl⟩
  have key : 2 * t = T * k := by
    rw [hk]
    linear_combination (-(b - a)) * hTx + (a + b) * hTy + (-2 * t) * hab
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    nlinarith
  have hk3 : -2 < k := by
    by_contra h
    push Not at h
    nlinarith
  have hpar' : (x + y) % 2 = 0 := hpar
  rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with h | h | h
  · -- `2 t = −T`: `2 x = −(d − n)`, `2 y = d + n`, so `x + y = n` is odd
    subst h
    have hx : 2 * x = -(d - n) := by
      have : T * (2 * x) = T * (-(d - n)) := by linear_combination 2 * hTx + (d - n) * key
      exact mul_left_cancel₀ hTpos.ne' this
    have hy : 2 * y = d + n := by
      have : T * (2 * y) = T * (d + n) := by linear_combination 2 * hTy + (-(d + n)) * key
      exact mul_left_cancel₀ hTpos.ne' this
    omega
  · subst h
    have ht0 : t = 0 := by omega
    have hx0 : x = 0 := by
      have : T * x = T * 0 := by rw [hTx, ht0]; ring
      exact mul_left_cancel₀ hTpos.ne' this
    have hy0 : y = 0 := by
      have : T * y = T * 0 := by rw [hTy, ht0]; ring
      exact mul_left_cancel₀ hTpos.ne' this
    exact ⟨hx0, hy0⟩
  · -- `2 t = T`: `2 x = d − n`, `2 y = −(d + n)`, so `x + y = −n` is odd
    subst h
    have hx : 2 * x = d - n := by
      have : T * (2 * x) = T * (d - n) := by linear_combination 2 * hTx + (d - n) * key
      exact mul_left_cancel₀ hTpos.ne' this
    have hy : 2 * y = -(d + n) := by
      have : T * (2 * y) = T * (-(d + n)) := by linear_combination 2 * hTy + (-(d + n)) * key
      exact mul_left_cancel₀ hTpos.ne' this
    omega

end FLatticePaper.VZeroS
