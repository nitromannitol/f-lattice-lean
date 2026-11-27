import Mathlib

/-! # The arithmetic of the free root classes (parent coordinates)

For an odd parent `(N, D)` with `0 < N < D`, `N + D` odd, and the period `T = D² + 2DN − N²`, a parent site `x = (x₁, x₂)` has
`u = N x₁ − D x₂` (the odd parent's `t`-grade) and `v = (D + N) x₁ + (D − N) x₂` (its `s`-grade).

* `arith_even`: if `u ∈ [1 − (D + N), 0]` and `v = 2j + 2T k` with `0 ≤ j ≤ N`, then `u = 0` and `v ≡ 0 (mod 2T)`.
* `arith_odd`: if `x₁ + x₂` is odd, `gcd(N, D) = 1`, `u ∈ [1 − D, N]` and `0 ≤ u − N + T l ≤ D − 1` for some `l`, then `u = N`
  and `v ≡ D + N (mod 2T)`.

Both are integrality arguments: with `q = x₁ − 2Dk` and `m = x₂ − 2Nk` one has `−u = mD − Nq` and `2j = (D+N) q + (D−N) m`. -/

namespace FLatticePaper.RootArith

theorem arith_even (N D x1 x2 j k : ℤ) (hN : 0 < N) (hND : N < D) (hodd : (N + D) % 2 = 1)
    (hu1 : 1 - (D + N) ≤ N * x1 - D * x2) (hu2 : N * x1 - D * x2 ≤ 0)
    (hj0 : 0 ≤ j) (hjN : j ≤ N)
    (hv : (D + N) * x1 + (D - N) * x2 = 2 * j + 2 * (D * D + 2 * D * N - N * N) * k) :
    N * x1 - D * x2 = 0 ∧ (D + N) * x1 + (D - N) * x2 = 2 * (D * D + 2 * D * N - N * N) * k := by
  obtain ⟨q, hq⟩ : ∃ q, q = x1 - 2 * D * k := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = x2 - 2 * N * k := ⟨_, rfl⟩
  have ha : -(N * x1 - D * x2) = m * D - N * q := by subst hq hm; ring
  have hb : 2 * j = (D + N) * q + (D - N) * m := by subst hq hm; linear_combination (-1 : ℤ) * hv
  have hs0 : 0 ≤ -(N * x1 - D * x2) := by linarith
  have hs1 : -(N * x1 - D * x2) ≤ D + N - 1 := by linarith
  have hDN : 0 < D - N := by linarith
  -- q ≤ 0: otherwise m < 0 and then the s-grade is negative
  have hq0 : q ≤ 0 := by
    by_contra h
    push Not at h
    have hm0 : m < 0 := by
      by_contra h'
      push Not at h'
      nlinarith
    nlinarith
  -- q ≥ 0: otherwise m ≥ 1 and the s-grade is at least D + N
  have hq1 : 0 ≤ q := by
    by_contra h
    push Not at h
    have hm1 : 0 < m := by
      by_contra h'
      push Not at h'
      nlinarith
    nlinarith
  have hq' : q = 0 := le_antisymm hq0 hq1
  subst hq'
  -- now 2j = (D - N) m and -u = m D with 0 ≤ mD ≤ D + N - 1
  have hm0 : 0 ≤ m := by
    by_contra h
    push Not at h
    nlinarith
  have hm1 : m ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hm01 : m = 0 := by
    rcases (show m = 0 ∨ m = 1 by omega) with h | h
    · exact h
    · subst h
      omega
  subst hm01
  have hj : j = 0 := by linarith
  have hu : N * x1 - D * x2 = 0 := by linarith
  refine ⟨hu, ?_⟩
  rw [hv, hj]
  ring

/-- The odd case: the window forces `u = N`, and then `N (v − (D + N)) = T x₂` with `gcd(N, T) = 1`. -/
theorem arith_odd (N D x1 x2 l : ℤ) (hN : 0 < N) (hND : N < D) (hodd : (N + D) % 2 = 1)
    (hcop : IsCoprime N D) (hxodd : (x1 + x2) % 2 = 1)
    (hu1 : 1 - D ≤ N * x1 - D * x2) (hu2 : N * x1 - D * x2 ≤ N)
    (hl0 : 0 ≤ N * x1 - D * x2 - N + (D * D + 2 * D * N - N * N) * l)
    (hl1 : N * x1 - D * x2 - N + (D * D + 2 * D * N - N * N) * l ≤ D - 1) :
    N * x1 - D * x2 = N ∧
      ∃ k, (D + N) * x1 + (D - N) * x2 - (D + N) = 2 * (D * D + 2 * D * N - N * N) * k := by
  obtain ⟨T, hT⟩ : ∃ T, T = D * D + 2 * D * N - N * N := ⟨_, rfl⟩
  rw [← hT] at hl0 hl1 ⊢
  have hTbig : 2 * D + N - 2 < T := by nlinarith
  have hTpos : 0 < T := by linarith
  -- the window forces l = 0 and then u = N
  have hl : l = 0 := by
    rcases lt_trichotomy l 0 with h | h | h
    · exfalso
      have : T * l ≤ -T := by nlinarith
      linarith
    · exact h
    · exfalso
      have : T ≤ T * l := by nlinarith
      linarith
  subst hl
  have hu : N * x1 - D * x2 = N := by linarith
  refine ⟨hu, ?_⟩
  -- the identity N v − (D + N) u = T x₂, with u = N
  have hNeq : N * ((D + N) * x1 + (D - N) * x2 - (D + N)) = T * x2 := by
    have e : N * ((D + N) * x1 + (D - N) * x2) - (D + N) * (N * x1 - D * x2) = T * x2 := by
      rw [hT]; ring
    rw [hu] at e
    linear_combination e
  -- parity: D + N = 2p + 1, D − N = 2r + 1, x₁ + x₂ = 2s + 1
  obtain ⟨p, hp⟩ : ∃ p, D + N = 2 * p + 1 := ⟨(D + N - 1) / 2, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, x1 + x2 = 2 * s + 1 := ⟨(x1 + x2 - 1) / 2, by omega⟩
  have hr : D - N = 2 * ((D - N - 1) / 2) + 1 := by omega
  have hTodd : T = 2 * (2 * p ^ 2 + 2 * p - N ^ 2) + 1 := by
    have hDN : D = 2 * p + 1 - N := by linarith
    rw [hT, hDN]; ring
  set w := (D + N) * x1 + (D - N) * x2 - (D + N) with hw
  set r := (D - N - 1) / 2 with hr'
  have hW : w = 2 * (s + p * x1 + r * x2 - p) := by
    have e : w = (x1 + x2 - 1) + 2 * (p * x1 + r * x2 - p) := by
      rw [hw]
      linear_combination x1 * hp + x2 * hr - hp
    rw [e, hs]
    ring
  -- Bézout: a N + b D = 1 gives b² T + β N = (a N + b D)² = 1
  obtain ⟨a, b, hab⟩ := hcop
  set k := b ^ 2 * w + (a ^ 2 * N + 2 * a * b * D - 2 * b ^ 2 * D + b ^ 2 * N) * x2 with hk
  have hk2 : w = T * k := by
    have hNeq' := hNeq
    rw [hT] at hNeq'
    rw [hk, hT]
    linear_combination (-w * (a * N + b * D + 1)) * hab + (a ^ 2 * N + 2 * a * b * D - 2 * b ^ 2 * D + b ^ 2 * N) * hNeq'
  refine ⟨s + p * x1 + r * x2 - p - (2 * p ^ 2 + 2 * p - N ^ 2) * k, ?_⟩
  rw [hTodd] at hk2 ⊢
  linear_combination (2 * (2 * p ^ 2 + 2 * p - N ^ 2) + 1) * hW + (-2 * (2 * p ^ 2 + 2 * p - N ^ 2)) * hk2

end FLatticePaper.RootArith
