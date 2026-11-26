import Mathlib.Tactic

/-! # The two even corners of the opposite collar are excluded by divisibility

For a parent `(N, D)` with conjugate data `C` (so `C d = D T + ε (d − n)`, `C n = N T − ε (d + n)`, `T = d² + 2 d n − n²`),
the grades of a site `u = (u₁, u₂)` are `t(u) = n u₁ − d u₂`, `s(u) = (d + n) u₁ + (d − n) u₂`, and the parent query is
`σ(u) = (D + N) u₁ + (D − N) u₂`. The identity `T σ = 2 ε t + C s` holds, and `σ(u) ≡ u₁ + u₂ (mod 2)` since `D ± N` are odd.

* `ε = +1`, the even corner `s(y) = −2d` with `y = u + (−1, −1)`: here `s(u) = 0`, so `t(u) = T J` for the integer
  `J = σ(u)/2`, and `t(y) = T J + (d − n)` misses the strict window `[d + n − 1 − T, 1]` of `y`.
* `ε = −1`, the even corner `s(y) = 2L` with `y = u + (1, 1)`: here `s(u) = 2n`, so `t(y) = T (N − J) + 2n` misses the same
  window. -/

namespace FLatticePaper.OppLattice

/-- The even corner for `ε = +1`: no even `y = u + (−1, −1)` with `s(u) = 0` has `t(y)` in the strict window. -/
theorem no_plus_corner (n d N D C T u₁ u₂ : ℤ) (hT0 : 0 < T)
    (hCd : C * d = D * T + (d - n)) (hCn : C * n = N * T - (d + n))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
    (hs : (d + n) * u₁ + (d - n) * u₂ = 0) (hye : (u₁ - 1 + (u₂ - 1)) % 2 = 0)
    (hy1 : d + n - 1 - T ≤ n * (u₁ - 1) - d * (u₂ - 1))
    (hy2 : n * (u₁ - 1) - d * (u₂ - 1) ≤ 1) : False := by
  have hid : T * ((D + N) * u₁ + (D - N) * u₂) =
      2 * (n * u₁ - d * u₂) + C * ((d + n) * u₁ + (d - n) * u₂) := by
    linear_combination (-(u₁ + u₂)) * hCd + (u₂ - u₁) * hCn
  rw [hs, mul_zero, add_zero] at hid
  obtain ⟨a, ha⟩ : ∃ a, D + N = 2 * a + 1 := ⟨(D + N) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, D - N = 2 * b + 1 := ⟨(D - N) / 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, u₁ + u₂ = 2 * c := ⟨(u₁ + u₂) / 2, by omega⟩
  have hσ2 : (D + N) * u₁ + (D - N) * u₂ = 2 * (a * u₁ + b * u₂ + c) := by
    rw [ha, hb]; linear_combination hc
  rw [hσ2] at hid
  -- `t(u) = T J` with `J = a u₁ + b u₂ + c`
  obtain ⟨J, hJ⟩ : ∃ J, J = a * u₁ + b * u₂ + c := ⟨_, rfl⟩
  rw [← hJ] at hid
  have htu : n * u₁ - d * u₂ = T * J := by linarith
  have hty : n * (u₁ - 1) - d * (u₂ - 1) = T * J + (d - n) := by linear_combination htu
  rw [hty] at hy1 hy2
  rcases (show J ≤ -1 ∨ J = 0 ∨ 1 ≤ J by omega) with h | h | h
  · have : T * J ≤ -T := by nlinarith
    linarith
  · subst h
    linarith
  · have : T ≤ T * J := by nlinarith
    nlinarith

/-- The even corner for `ε = −1`: no even `y = u + (1, 1)` with `s(u) = 2n` has `t(y)` in the strict window. -/
theorem no_minus_corner (n d N D C T u₁ u₂ : ℤ) (hT0 : 0 < T)
    (hCd : C * d = D * T - (d - n)) (hCn : C * n = N * T + (d + n))
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hpD : (D + N) % 2 = 1) (hpE : (D - N) % 2 = 1)
    (hs : (d + n) * u₁ + (d - n) * u₂ = 2 * n) (hye : (u₁ + 1 + (u₂ + 1)) % 2 = 0)
    (hy1 : d + n - 1 - T ≤ n * (u₁ + 1) - d * (u₂ + 1))
    (hy2 : n * (u₁ + 1) - d * (u₂ + 1) ≤ 1) : False := by
  have hid : T * ((D + N) * u₁ + (D - N) * u₂) =
      -2 * (n * u₁ - d * u₂) + C * ((d + n) * u₁ + (d - n) * u₂) := by
    linear_combination (-(u₁ + u₂)) * hCd + (u₂ - u₁) * hCn
  rw [hs] at hid
  obtain ⟨a, ha⟩ : ∃ a, D + N = 2 * a + 1 := ⟨(D + N) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, D - N = 2 * b + 1 := ⟨(D - N) / 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, u₁ + u₂ = 2 * c := ⟨(u₁ + u₂) / 2, by omega⟩
  have hσ2 : (D + N) * u₁ + (D - N) * u₂ = 2 * (a * u₁ + b * u₂ + c) := by
    rw [ha, hb]; linear_combination hc
  rw [hσ2] at hid
  obtain ⟨J, hJ⟩ : ∃ J, J = a * u₁ + b * u₂ + c := ⟨_, rfl⟩
  rw [← hJ] at hid
  -- `T J = n C − t(u)`
  have E2 : T * J = n * C - (n * u₁ - d * u₂) := by linarith
  -- `t(y) = T (N − J) + 2 n`
  have hty : n * (u₁ + 1) - d * (u₂ + 1) = T * (N - J) + 2 * n := by
    linear_combination E2 + hCn
  rw [hty] at hy1 hy2
  rcases (show N - J ≤ -1 ∨ 0 ≤ N - J by omega) with h | h
  · have : T * (N - J) ≤ -T := by nlinarith
    linarith
  · have : 0 ≤ T * (N - J) := mul_nonneg hT0.le h
    linarith

end FLatticePaper.OppLattice
