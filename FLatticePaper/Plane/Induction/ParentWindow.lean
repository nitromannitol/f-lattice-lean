import FLatticePaper.Plane.Induction.RootWindow

/-! # The parent window of a bottom centre

With `L = d + n`, `T = d² + 2dn − n²`, `C = D L + N (d − n)` and `ε = N d − D n`, the odd parent's grade of a centre `c = (c₁, c₂)` is
`u = N c₁ − D c₂`, and `T u = C t + ε s` (`t = n c₁ − d c₂`, `s = L c₁ + (d − n) c₂`). The child window of `RootWindow.bottom_window`
then gives the parent window:

* even centre: `1 − (D + N) ≤ u ≤ 0` when `ε = 1`, and `−(D + N) ≤ u ≤ −1` when `ε = −1`;
* odd centre: `1 − D ≤ u ≤ N` when `ε = 1`, and `−D ≤ u ≤ N − 1` when `ε = −1`.

The proof uses the identities `C n = N T − ε L` and `C d = D T + ε (d − n)`, and `T (D + N) − C (L − 2) = 2 (ε (n + 1) + D (2n + d) − N n)`,
all polynomial consequences of `ε = N d − D n`. -/

namespace FLatticePaper.ParentWindow

theorem key_identity (n d N D c1 c2 ε : ℤ) (hε : N * d - D * n = ε) :
    (d * d + 2 * d * n - n * n) * (N * c1 - D * c2) =
      (D * (d + n) + N * (d - n)) * (n * c1 - d * c2) + ε * ((d + n) * c1 + (d - n) * c2) := by
  rw [← hε]; ring

theorem identity_n (n d N D ε : ℤ) (hε : N * d - D * n = ε) :
    (D * (d + n) + N * (d - n)) * n = N * (d * d + 2 * d * n - n * n) - ε * (d + n) := by
  rw [← hε]; ring

theorem identity_d (n d N D ε : ℤ) (hε : N * d - D * n = ε) :
    (D * (d + n) + N * (d - n)) * d = D * (d * d + 2 * d * n - n * n) + ε * (d - n) := by
  rw [← hε]; ring

theorem identity_L (n d N D ε : ℤ) (hε : N * d - D * n = ε) :
    (d * d + 2 * d * n - n * n) * (D + N) - (D * (d + n) + N * (d - n)) * ((d + n) - 2) =
      2 * (ε * (n + 1) + D * (2 * n + d) - N * n) := by
  rw [← hε]; ring

/-- **The even parent window.** -/
theorem parent_window_even (n d N D c1 c2 ε : ℤ) (hε : N * d - D * n = ε) (hε1 : ε = 1 ∨ ε = -1)
    (hn3 : 3 ≤ n) (hnd : n < d) (hN : 0 < N) (hND : N < D)
    (ht1 : 2 - (d + n) ≤ n * c1 - d * c2) (ht2 : n * c1 - d * c2 ≤ 0)
    (hs1 : 2 * n < (d + n) * c1 + (d - n) * c2) (hs2 : (d + n) * c1 + (d - n) * c2 < d * d + 2 * d * n - n * n) :
    (ε = 1 → 1 - (D + N) ≤ N * c1 - D * c2 ∧ N * c1 - D * c2 ≤ 0) ∧
      (ε = -1 → -(D + N) ≤ N * c1 - D * c2 ∧ N * c1 - D * c2 ≤ -1) := by
  have key := key_identity n d N D c1 c2 ε hε
  have hidL := identity_L n d N D ε hε
  have hC : 0 ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hT : 0 < d * d + 2 * d * n - n * n := by nlinarith
  have hlow : (D * (d + n) + N * (d - n)) * (2 - (d + n)) ≤ (D * (d + n) + N * (d - n)) * (n * c1 - d * c2) :=
    mul_le_mul_of_nonneg_left ht1 hC
  have hCt : (D * (d + n) + N * (d - n)) * (n * c1 - d * c2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left ht2 hC
    linarith
  have hNn : N * n ≤ D * n := by nlinarith
  constructor
  · intro h1
    subst h1
    have hpos : 0 ≤ 2 * (1 * (n + 1) + D * (2 * n + d) - N * n) := by nlinarith
    have hC2 : -((d * d + 2 * d * n - n * n) * (D + N)) ≤ (D * (d + n) + N * (d - n)) * (2 - (d + n)) := by
      linarith
    have hTX : 0 < (d * d + 2 * d * n - n * n) * (N * c1 - D * c2 + (D + N)) := by
      linarith
    have hX : 0 < N * c1 - D * c2 + (D + N) := pos_of_mul_pos_right hTX hT.le
    have hTu : (d * d + 2 * d * n - n * n) * (N * c1 - D * c2) < (d * d + 2 * d * n - n * n) * 1 := by
      linarith
    have hX1 : N * c1 - D * c2 < 1 := lt_of_mul_lt_mul_left hTu hT.le
    exact ⟨by linarith, by linarith⟩
  · intro h1
    subst h1
    have hpos : 0 ≤ 2 * (-1 * (n + 1) + D * (2 * n + d) - N * n) := by nlinarith
    have hC2 : 0 ≤ (d * d + 2 * d * n - n * n) * (D + N) - (D * (d + n) + N * (d - n)) * ((d + n) - 2) := by
      linarith
    have hTX : 0 < (d * d + 2 * d * n - n * n) * (N * c1 - D * c2 + (D + N) + 1) := by
      linarith
    have hX : 0 < N * c1 - D * c2 + (D + N) + 1 := pos_of_mul_pos_right hTX hT.le
    have hTu : (d * d + 2 * d * n - n * n) * (N * c1 - D * c2) < (d * d + 2 * d * n - n * n) * 0 := by
      linarith
    have hX1 : N * c1 - D * c2 < 0 := lt_of_mul_lt_mul_left hTu hT.le
    exact ⟨by linarith, by linarith⟩

/-- **The odd parent window.** -/
theorem parent_window_odd (n d N D c1 c2 ε : ℤ) (hε : N * d - D * n = ε) (hε1 : ε = 1 ∨ ε = -1)
    (hn3 : 3 ≤ n) (hnd : n < d) (hN : 0 < N) (hND : N < D)
    (ht1 : -d ≤ n * c1 - d * c2) (ht2 : n * c1 - d * c2 ≤ n - 2)
    (hs1 : d + n - 2 < (d + n) * c1 + (d - n) * c2)
    (hs2 : (d + n) * c1 + (d - n) * c2 < d * d + 2 * d * n - n * n + 2 - d + n) :
    (ε = 1 → 1 - D ≤ N * c1 - D * c2 ∧ N * c1 - D * c2 ≤ N) ∧
      (ε = -1 → -D ≤ N * c1 - D * c2 ∧ N * c1 - D * c2 ≤ N - 1) := by
  have key := key_identity n d N D c1 c2 ε hε
  have hIn := identity_n n d N D ε hε
  have hId := identity_d n d N D ε hε
  have hC : 0 ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hT : 0 < d * d + 2 * d * n - n * n := by nlinarith
  have hClo : (D * (d + n) + N * (d - n)) * (-d) ≤ (D * (d + n) + N * (d - n)) * (n * c1 - d * c2) :=
    mul_le_mul_of_nonneg_left ht1 hC
  have hChi : (D * (d + n) + N * (d - n)) * (n * c1 - d * c2) ≤ (D * (d + n) + N * (d - n)) * (n - 2) :=
    mul_le_mul_of_nonneg_left ht2 hC
  have hCpos : 2 ≤ D * (d + n) + N * (d - n) := by nlinarith
  constructor
  · intro h1
    subst h1
    have hTX : 0 < (d * d + 2 * d * n - n * n) * (N * c1 - D * c2 + D) := by
      nlinarith
    have hX : 0 < N * c1 - D * c2 + D := pos_of_mul_pos_right hTX hT.le
    have hTu : (d * d + 2 * d * n - n * n) * (N * c1 - D * c2) < (d * d + 2 * d * n - n * n) * (N + 1) := by
      nlinarith
    have hX1 : N * c1 - D * c2 < N + 1 := lt_of_mul_lt_mul_left hTu hT.le
    exact ⟨by linarith, by linarith⟩
  · intro h1
    subst h1
    have hTX : 0 < (d * d + 2 * d * n - n * n) * (N * c1 - D * c2 + D + 1) := by
      nlinarith
    have hX : 0 < N * c1 - D * c2 + D + 1 := pos_of_mul_pos_right hTX hT.le
    have hTu : (d * d + 2 * d * n - n * n) * (N * c1 - D * c2) < (d * d + 2 * d * n - n * n) * N := by
      nlinarith
    have hX1 : N * c1 - D * c2 < N := lt_of_mul_lt_mul_left hTu hT.le
    exact ⟨by linarith, by linarith⟩

end FLatticePaper.ParentWindow
