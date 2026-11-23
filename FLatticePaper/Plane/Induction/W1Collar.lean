import FLatticePaper.Plane.Induction.ParentCoordinates

/-! Task 57: W1_CONSTRUCTOR §3 and §4, the arithmetic of the aligned collars.

A child `n/d` (`0 < n < d`) with odd parent `N/D` (`0 < N`, `0 < D`), `ε = N d − D n = ±1`, `L = d + n`, `Lp = D + N`,
`T = d² + 2dn − n²`, `C = D L + N (d − n)`. A site `(x, y)` has physical grades `t = n x − d y`, `s = L x + (d − n) y` and
parent grades `tp = N x − D y`, `sp = Lp x + (D − N) y`. The transform identities `T·tp = C t + ε s` and `T·sp = C s + 2ε t`
are proved by `ring`; the collar statements are then integer inequalities. Nothing here uses the parent's own W1. -/

namespace FLatticePaper.W1Collar

theorem tp_identity (n d N D x y : ℤ) :
    (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y) =
      (D * (d + n) + N * (d - n)) * (n * x - d * y) + (N * d - D * n) * ((d + n) * x + (d - n) * y) := by
  ring

theorem sp_identity (n d N D x y : ℤ) :
    (d ^ 2 + 2 * d * n - n ^ 2) * ((D + N) * x + (D - N) * y) =
      (D * (d + n) + N * (d - n)) * ((d + n) * x + (d - n) * y) + 2 * (N * d - D * n) * (n * x - d * y) := by
  ring

theorem CL_identity (n d N D : ℤ) :
    (D * (d + n) + N * (d - n)) * (d + n) = (D + N) * (d ^ 2 + 2 * d * n - n ^ 2) - 2 * (N * d - D * n) * n := by
  ring

theorem Cn_identity (n d N D : ℤ) :
    (D * (d + n) + N * (d - n)) * n = N * (d ^ 2 + 2 * d * n - n ^ 2) - (N * d - D * n) * (d + n) := by
  ring

theorem Cd_identity (n d N D : ℤ) :
    (D * (d + n) + N * (d - n)) * d = D * (d ^ 2 + 2 * d * n - n ^ 2) + (N * d - D * n) * (d - n) := by
  ring

/-! ## §3: the bottom collar, `t* = tp(z − lv)`, with `tp(lv) = (1 − W) ε`.

For `ε = +1` (so `W = 1`) `t* = tp`; for `ε = −1` (so `W = 0`) `t* = tp + 1`. The hypotheses are the strict-interior
bounds of §1 together with the one-pixel bound `t ≥ 2 − L` (even) or `t ≥ −d` (odd) from the H-arc. -/

theorem bottom_even_pos (n d N D : ℤ) (hn : 0 < n) (hnd : n < d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = 1) (x y : ℤ)
    (h1 : 2 - (d + n) ≤ n * x - d * y) (h2 : n * x - d * y ≤ 0)
    (h3 : 2 * n < (d + n) * x + (d - n) * y)
    (h4 : (d + n) * x + (d - n) * y < d ^ 2 + 2 * d * n - n ^ 2) :
    1 - (D + N) ≤ N * x - D * y ∧ N * x - D * y ≤ 0 := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have key := tp_identity n d N D x y
  rw [hε, one_mul] at key
  have hCL := CL_identity n d N D
  rw [hε] at hCL
  constructor
  · have hCt := mul_le_mul_of_nonneg_left h1 hC.le
    have hpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y + (D + N)) := by nlinarith
    have hpos' : 0 < N * x - D * y + (D + N) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hCt := mul_le_mul_of_nonneg_left h2 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y) < (d ^ 2 + 2 * d * n - n ^ 2) * 1 := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

theorem bottom_even_neg (n d N D : ℤ) (hn : 0 < n) (hnd : n < d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = -1) (x y : ℤ)
    (h1 : 2 - (d + n) ≤ n * x - d * y) (h2 : n * x - d * y ≤ 0)
    (h3 : 2 * n < (d + n) * x + (d - n) * y)
    (h4 : (d + n) * x + (d - n) * y < d ^ 2 + 2 * d * n - n ^ 2) :
    1 - (D + N) ≤ N * x - D * y + 1 ∧ N * x - D * y + 1 ≤ 0 := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have key := tp_identity n d N D x y
  rw [hε] at key
  have hCL := CL_identity n d N D
  rw [hε] at hCL
  constructor
  · have hCt := mul_le_mul_of_nonneg_left h1 hC.le
    have hpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y + (D + N) + 1) := by nlinarith
    have hpos' : 0 < N * x - D * y + (D + N) + 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hCt := mul_le_mul_of_nonneg_left h2 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y) < (d ^ 2 + 2 * d * n - n ^ 2) * 0 := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

theorem bottom_odd_pos (n d N D : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = 1) (x y : ℤ)
    (h1 : -d ≤ n * x - d * y) (h2 : n * x - d * y ≤ n - 2)
    (h3 : d + n - 2 < (d + n) * x + (d - n) * y)
    (h4 : (d + n) * x + (d - n) * y < d ^ 2 + 2 * d * n - n ^ 2 + 2 - d + n) :
    1 - D ≤ N * x - D * y ∧ N * x - D * y ≤ N := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have key := tp_identity n d N D x y
  rw [hε, one_mul] at key
  have hCn := Cn_identity n d N D
  rw [hε] at hCn
  have hCd := Cd_identity n d N D
  rw [hε] at hCd
  constructor
  · have hCt := mul_le_mul_of_nonneg_left h1 hC.le
    have hpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y + D) := by nlinarith
    have hpos' : 0 < N * x - D * y + D := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hCt := mul_le_mul_of_nonneg_left h2 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y) < (d ^ 2 + 2 * d * n - n ^ 2) * (N + 1) := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

theorem bottom_odd_neg (n d N D : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = -1) (x y : ℤ)
    (h1 : -d ≤ n * x - d * y) (h2 : n * x - d * y ≤ n - 2)
    (h3 : d + n - 2 < (d + n) * x + (d - n) * y)
    (h4 : (d + n) * x + (d - n) * y < d ^ 2 + 2 * d * n - n ^ 2 + 2 - d + n) :
    1 - D ≤ N * x - D * y + 1 ∧ N * x - D * y + 1 ≤ N := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have key := tp_identity n d N D x y
  rw [hε] at key
  have hCn := Cn_identity n d N D
  rw [hε] at hCn
  have hCd := Cd_identity n d N D
  rw [hε] at hCd
  constructor
  · have hCt := mul_le_mul_of_nonneg_left h1 hC.le
    have hpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y + D + 1) := by nlinarith
    have hpos' : 0 < N * x - D * y + D + 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hCt := mul_le_mul_of_nonneg_left h2 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * (N * x - D * y) < (d ^ 2 + 2 * d * n - n ^ 2) * N := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

/-! ## §3: the left collar, `s* = sp(z − (1 − W) Vq)`, with `sp(Vq) = −2 ε`.

For `ε = +1` (`W = 1`) `s* = sp`; for `ε = −1` (`W = 0`) `s* = sp − 2`. Writing `x + y = 2k` (even sites) or `2k + 1`
(odd sites) gives `sp = Lp (x + y) − 2 N y`, so `sp` is even at even sites and `≡ Lp` at odd sites. `s` is even at every
site since `L = d + n` and `d − n` are even (`n`, `d` odd), and this is recorded as `d + n = 2p`, `d − n = 2q`. -/

theorem left_even_pos (n d N D x y k : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = 1) (hk : x + y = 2 * k)
    (h1 : d + n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * x - d * y) (h2 : n * x - d * y ≤ 0)
    (h3 : 2 * n < (d + n) * x + (d - n) * y) (h4 : (d + n) * x + (d - n) * y ≤ 2 * (d + n) - 2) :
    2 * N ≤ (D + N) * x + (D - N) * y ∧ (D + N) * x + (D - N) * y ≤ 2 * (D + N) - 2 := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have hpar : (D + N) * x + (D - N) * y = 2 * ((D + N) * k - N * y) := by
    linear_combination (D + N) * hk
  obtain ⟨j, hj⟩ : ∃ j, (D + N) * x + (D - N) * y = 2 * j := ⟨_, hpar⟩
  have key := sp_identity n d N D x y
  rw [hε, hj] at key
  have hCn := Cn_identity n d N D
  rw [hε] at hCn
  have hCL := CL_identity n d N D
  rw [hε] at hCL
  have hs2 : 2 * n + 1 ≤ (d + n) * x + (d - n) * y := by linarith
  constructor
  · have hA := mul_le_mul_of_nonneg_left hs2 hC.le
    have hB : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (j - N + 1) := by nlinarith
    have hB' : 0 < j - N + 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hA := mul_le_mul_of_nonneg_left h4 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * j < (d ^ 2 + 2 * d * n - n ^ 2) * (D + N) := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

theorem left_even_neg (n d N D x y k : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = -1) (hk : x + y = 2 * k)
    (h1 : d + n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * x - d * y) (h2 : n * x - d * y ≤ 0)
    (h3 : 2 * n < (d + n) * x + (d - n) * y) (h4 : (d + n) * x + (d - n) * y ≤ 2 * (d + n) - 2) :
    2 * N + 2 ≤ (D + N) * x + (D - N) * y ∧ (D + N) * x + (D - N) * y ≤ 2 * (D + N) := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have hpar : (D + N) * x + (D - N) * y = 2 * ((D + N) * k - N * y) := by
    linear_combination (D + N) * hk
  obtain ⟨j, hj⟩ : ∃ j, (D + N) * x + (D - N) * y = 2 * j := ⟨_, hpar⟩
  have key := sp_identity n d N D x y
  rw [hε, hj] at key
  have hCn := Cn_identity n d N D
  rw [hε] at hCn
  have hCL := CL_identity n d N D
  rw [hε] at hCL
  have hs2 : 2 * n + 1 ≤ (d + n) * x + (d - n) * y := by linarith
  constructor
  · have hA := mul_le_mul_of_nonneg_left hs2 hC.le
    have hB : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (j - N) := by nlinarith
    have hB' : 0 < j - N := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hA := mul_le_mul_of_nonneg_left h4 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * j < (d ^ 2 + 2 * d * n - n ^ 2) * (D + N + 1) := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

theorem left_odd_pos (n d N D x y k p q : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = 1) (hk : x + y = 2 * k + 1) (hp : d + n = 2 * p) (hq : d - n = 2 * q)
    (h1 : d - (d ^ 2 + 2 * d * n - n ^ 2) + 1 ≤ n * x - d * y) (h2 : n * x - d * y ≤ n - 2)
    (h3 : d + n - 2 < (d + n) * x + (d - n) * y) (h4 : (d + n) * x + (d - n) * y ≤ 3 * d + n - 2) :
    (D + N) ≤ (D + N) * x + (D - N) * y ∧ (D + N) * x + (D - N) * y ≤ 3 * D + N - 2 := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have hCge : d + n ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hpar : (D + N) * x + (D - N) * y = (D + N) + 2 * ((D + N) * k - N * y) := by
    linear_combination (D + N) * hk
  obtain ⟨j, hj⟩ : ∃ j, (D + N) * x + (D - N) * y = (D + N) + 2 * j := ⟨_, hpar⟩
  -- s is even: s = 2 (p x + q y), and s > d + n - 2 forces s ≥ d + n.
  have hs_even : (d + n) * x + (d - n) * y = 2 * (p * x + q * y) := by
    linear_combination x * hp + y * hq
  have hm : p ≤ p * x + q * y := by
    have : d + n - 2 < 2 * (p * x + q * y) := by rw [← hs_even]; exact h3
    linarith
  have hsL : d + n ≤ (d + n) * x + (d - n) * y := by
    rw [hs_even]; linarith
  have key := sp_identity n d N D x y
  rw [hε, hj] at key
  have hCL := CL_identity n d N D
  rw [hε] at hCL
  have hCn := Cn_identity n d N D
  rw [hε] at hCn
  have hCd := Cd_identity n d N D
  rw [hε] at hCd
  constructor
  · have hA := mul_le_mul_of_nonneg_left hsL hC.le
    have hB : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (j + 1) := by nlinarith
    have hB' : 0 < j + 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hA := mul_le_mul_of_nonneg_left h4 hC.le
    have hCt := mul_le_mul_of_nonneg_left h2 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * j < (d ^ 2 + 2 * d * n - n ^ 2) * D := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

theorem left_odd_neg (n d N D x y k p q : ℤ) (hn : 0 < n) (hnd : n + 2 ≤ d) (hN : 0 < N) (hD : 0 < D)
    (hε : N * d - D * n = -1) (hk : x + y = 2 * k + 1) (hp : d + n = 2 * p) (hq : d - n = 2 * q)
    (h1 : d - (d ^ 2 + 2 * d * n - n ^ 2) + 1 ≤ n * x - d * y) (h2 : n * x - d * y ≤ n - 2)
    (h3 : d + n - 2 < (d + n) * x + (d - n) * y) (h4 : (d + n) * x + (d - n) * y ≤ 3 * d + n - 2) :
    (D + N) + 2 ≤ (D + N) * x + (D - N) * y ∧ (D + N) * x + (D - N) * y ≤ 3 * D + N := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have hpar : (D + N) * x + (D - N) * y = (D + N) + 2 * ((D + N) * k - N * y) := by
    linear_combination (D + N) * hk
  obtain ⟨j, hj⟩ : ∃ j, (D + N) * x + (D - N) * y = (D + N) + 2 * j := ⟨_, hpar⟩
  have hs_even : (d + n) * x + (d - n) * y = 2 * (p * x + q * y) := by
    linear_combination x * hp + y * hq
  have hm : p ≤ p * x + q * y := by
    have : d + n - 2 < 2 * (p * x + q * y) := by rw [← hs_even]; exact h3
    linarith
  have hsL : d + n ≤ (d + n) * x + (d - n) * y := by
    rw [hs_even]; linarith
  have key := sp_identity n d N D x y
  rw [hε, hj] at key
  have hCL := CL_identity n d N D
  rw [hε] at hCL
  have hCn := Cn_identity n d N D
  rw [hε] at hCn
  have hCd := Cd_identity n d N D
  rw [hε] at hCd
  constructor
  · have hA := mul_le_mul_of_nonneg_left hsL hC.le
    have hB : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * j := by nlinarith
    have hB' : 0 < j := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    linarith
  · have hA := mul_le_mul_of_nonneg_left h4 hC.le
    have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * j < (d ^ 2 + 2 * d * n - n ^ 2) * (D + 1) := by
      nlinarith
    have := lt_of_mul_lt_mul_left hlt hT.le
    linarith

/-! ## §4: the residue lemmas. An integer `v = m − M b` in the range of one period is the residue `m mod M`,
with the single named exception at the upper end. -/

theorem residue_nonneg (M v m b : ℤ) (hM : 0 < M) (hv : v = m - M * b) (h0 : 0 ≤ v) (h1 : v < M) :
    v = m % M := by
  have hr0 : 0 ≤ m % M := Int.emod_nonneg m hM.ne'
  have hr1 : m % M < M := Int.emod_lt_of_pos m hM
  have key : v - m % M = M * (m / M - b) := by
    rw [Int.emod_def]; linear_combination hv
  obtain ⟨e, he⟩ : ∃ e, e = m / M - b := ⟨_, rfl⟩
  rw [← he] at key
  rcases (show e ≤ -1 ∨ e = 0 ∨ 1 ≤ e by omega) with h | h | h
  · exfalso
    have : M * e ≤ M * (-1) := mul_le_mul_of_nonneg_left h hM.le
    linarith
  · rw [h, mul_zero] at key
    linarith
  · exfalso
    have : M * 1 ≤ M * e := mul_le_mul_of_nonneg_left h hM.le
    linarith

theorem residue_pos (M v m b : ℤ) (hM : 0 < M) (hv : v = m - M * b) (h0 : 1 ≤ v) (h1 : v ≤ M) :
    (m % M = 0 → v = M) ∧ (m % M ≠ 0 → v = m % M) := by
  have hr0 : 0 ≤ m % M := Int.emod_nonneg m hM.ne'
  have hr1 : m % M < M := Int.emod_lt_of_pos m hM
  have key : v - m % M = M * (m / M - b) := by
    rw [Int.emod_def]; linear_combination hv
  obtain ⟨e, he⟩ : ∃ e, e = m / M - b := ⟨_, rfl⟩
  rw [← he] at key
  rcases (show e ≤ -1 ∨ e = 0 ∨ e = 1 ∨ 2 ≤ e by omega) with h | h | h | h
  · exfalso
    have : M * e ≤ M * (-1) := mul_le_mul_of_nonneg_left h hM.le
    linarith
  · subst h
    rw [mul_zero] at key
    constructor
    · intro hr; rw [hr] at key; linarith
    · intro _; linarith
  · subst h
    rw [mul_one] at key
    constructor
    · intro hr
      have : m % M ≤ 0 := by linarith
      have : m % M = 0 := by linarith
      rw [this] at key; linarith
    · intro hr
      have : 0 < m % M := lt_of_le_of_ne hr0 (Ne.symm hr)
      exfalso; linarith
  · exfalso
    have : M * 2 ≤ M * e := mul_le_mul_of_nonneg_left h hM.le
    linarith

/-! ## §4: the even native H endpoints `(2l − b, b)`, `b = ⌊2nl / L⌋`, `1 ≤ l`, `2l < L`.

Their parent grade `tp = N(2l − b) − D b = 2Nl − Lp b` is the residue of `2Nl mod Lp`, except that the residue `0` at
`ε = +1` gives `tp = Lp`. -/

theorem H_endpoint (n d N D l b : ℤ) (hn : 0 < n) (hnd : n < d) (hN : 0 < N) (hD : 0 < D)
    (hl : 1 ≤ l) (hl2 : 2 * l < d + n) (hb : b = (2 * n * l) / (d + n))
    :
    (N * d - D * n = 1 → (2 * N * l) % (D + N) = 0 → N * (2 * l - b) - D * b = D + N) ∧
    (N * d - D * n = 1 → (2 * N * l) % (D + N) ≠ 0 → N * (2 * l - b) - D * b = (2 * N * l) % (D + N)) ∧
    (N * d - D * n = -1 → N * (2 * l - b) - D * b = (2 * N * l) % (D + N)) := by
  have hL : 0 < d + n := by omega
  have hLp : 0 < D + N := by omega
  have hdiv : (d + n) * ((2 * n * l) / (d + n)) + (2 * n * l) % (d + n) = 2 * n * l := by
    rw [Int.emod_def]; ring
  have hk0 : 0 ≤ (2 * n * l) % (d + n) := Int.emod_nonneg _ hL.ne'
  have hk1 : (2 * n * l) % (d + n) < d + n := Int.emod_lt_of_pos _ hL
  obtain ⟨k, hk⟩ : ∃ k, k = (2 * n * l) % (d + n) := ⟨_, rfl⟩
  rw [← hk] at hdiv hk0 hk1
  have hLb : (d + n) * b + k = 2 * n * l := by rw [hb]; exact hdiv
  have hid : (D + N) * (2 * n * l) = (d + n) * (2 * N * l) - 2 * (N * d - D * n) * l := by ring
  have key : (d + n) * (N * (2 * l - b) - D * b) = (D + N) * k + 2 * (N * d - D * n) * l := by
    linear_combination (-1 : ℤ) * hid - (D + N) * hLb
  have htpm : N * (2 * l - b) - D * b = 2 * N * l - (D + N) * b := by ring
  obtain ⟨tp, htp⟩ : ∃ tp, tp = N * (2 * l - b) - D * b := ⟨_, rfl⟩
  rw [← htp] at key ⊢
  rw [htpm] at htp
  refine ⟨fun h1 h0 => ?_, fun h1 hr => ?_, fun hm1 => ?_⟩
  · -- ε = +1, residue 0: tp = Lp
    rw [h1] at key
    have lo : 1 ≤ tp := by
      by_contra hc; rw [not_le] at hc
      nlinarith
    have hi : tp ≤ D + N := by
      by_contra hc; rw [not_le] at hc
      nlinarith
    have hv : tp = (2 * N * l) - (D + N) * b := by linarith
    exact ((residue_pos (D + N) tp (2 * N * l) b hLp hv lo hi).1 h0)
  · rw [h1] at key
    have lo : 1 ≤ tp := by
      by_contra hc; rw [not_le] at hc
      nlinarith
    have hi : tp ≤ D + N := by
      by_contra hc; rw [not_le] at hc
      nlinarith
    have hv : tp = (2 * N * l) - (D + N) * b := by linarith
    exact ((residue_pos (D + N) tp (2 * N * l) b hLp hv lo hi).2 hr)
  · rw [hm1] at key
    have lo : 0 ≤ tp := by
      by_contra hc; rw [not_le] at hc
      nlinarith
    have hi : tp < D + N := by
      by_contra hc; rw [not_lt] at hc
      nlinarith
    have hv : tp = (2 * N * l) - (D + N) * b := by linarith
    exact residue_nonneg (D + N) tp (2 * N * l) b hLp hv lo hi

/-! ## §4: the odd native V endpoints `(−b, 2l − 1 − b)`, `b = ⌊(d − n) l / d⌋`, `1 ≤ l ≤ d − 1`.

Their parent coordinate `f = (D − N) l − D b` is the residue of `(D − N) l mod D`, except that the residue `0` at
`ε = −1` gives `f = D`. Their parent sp grade is `2f − (D − N)`. -/

theorem V_endpoint_pos (n d N D l b : ℤ) (hn : 0 < n) (hnd : n + 1 ≤ d) (hD : 0 < D)
    (hl : 1 ≤ l) (hl2 : l ≤ d - 1) (hb : b = ((d - n) * l) / d) (hε : N * d - D * n = 1) :
    (((D - N) * l) % D = 0 → (D - N) * l - D * b = 0) ∧
    (((D - N) * l) % D ≠ 0 → (D - N) * l - D * b = ((D - N) * l) % D) := by
  have hd : 0 < d := by omega
  have hdiv : d * (((d - n) * l) / d) + ((d - n) * l) % d = (d - n) * l := by
    rw [Int.emod_def]; ring
  have hk0 : 0 ≤ ((d - n) * l) % d := Int.emod_nonneg _ hd.ne'
  have hk1 : ((d - n) * l) % d < d := Int.emod_lt_of_pos _ hd
  obtain ⟨k, hk⟩ : ∃ k, k = ((d - n) * l) % d := ⟨_, rfl⟩
  rw [← hk] at hdiv hk0 hk1
  have hdb : d * b + k = (d - n) * l := by rw [hb]; exact hdiv
  have hid : d * ((D - N) * l) = D * ((d - n) * l) - (N * d - D * n) * l := by ring
  obtain ⟨f, hf⟩ : ∃ f, f = (D - N) * l - D * b := ⟨_, rfl⟩
  have key : d * f = D * k - (N * d - D * n) * l := by
    rw [hf]; linear_combination hid - D * hdb
  rw [hε] at key
  have hk' : k ≤ d - 1 := by omega
  have lo : 0 ≤ f := by
    by_contra hc; rw [not_le] at hc
    nlinarith [mul_nonneg hD.le hk0]
  have hi : f < D := by
    by_contra hc; rw [not_lt] at hc
    nlinarith [mul_le_mul_of_nonneg_left hk' hD.le]
  have hfm := residue_nonneg D ((D - N) * l - D * b) ((D - N) * l) b hD rfl (by rw [← hf]; exact lo)
    (by rw [← hf]; exact hi)
  exact ⟨fun h0 => hfm.trans h0, fun _ => hfm⟩

theorem V_endpoint_neg (n d N D l b : ℤ) (hn : 0 < n) (hnd : n + 1 ≤ d) (hD : 0 < D)
    (hl : 1 ≤ l) (hl2 : l ≤ d - 1) (hb : b = ((d - n) * l) / d) (hε : N * d - D * n = -1) :
    (((D - N) * l) % D = 0 → (D - N) * l - D * b = D) ∧
    (((D - N) * l) % D ≠ 0 → (D - N) * l - D * b = ((D - N) * l) % D) := by
  have hd : 0 < d := by omega
  have hdiv : d * (((d - n) * l) / d) + ((d - n) * l) % d = (d - n) * l := by
    rw [Int.emod_def]; ring
  have hk0 : 0 ≤ ((d - n) * l) % d := Int.emod_nonneg _ hd.ne'
  have hk1 : ((d - n) * l) % d < d := Int.emod_lt_of_pos _ hd
  obtain ⟨k, hk⟩ : ∃ k, k = ((d - n) * l) % d := ⟨_, rfl⟩
  rw [← hk] at hdiv hk0 hk1
  have hdb : d * b + k = (d - n) * l := by rw [hb]; exact hdiv
  have hid : d * ((D - N) * l) = D * ((d - n) * l) - (N * d - D * n) * l := by ring
  obtain ⟨f, hf⟩ : ∃ f, f = (D - N) * l - D * b := ⟨_, rfl⟩
  have key : d * f = D * k - (N * d - D * n) * l := by
    rw [hf]; linear_combination hid - D * hdb
  rw [hε] at key
  have hk' : k ≤ d - 1 := by omega
  have lo : 1 ≤ f := by
    by_contra hc; rw [not_le] at hc
    nlinarith [mul_nonneg hD.le hk0]
  have hi : f ≤ D := by
    by_contra hc; rw [not_le] at hc
    nlinarith [mul_le_mul_of_nonneg_left hk' hD.le]
  have hgen := residue_pos D ((D - N) * l - D * b) ((D - N) * l) b hD rfl (by rw [← hf]; exact lo)
    (by rw [← hf]; exact hi)
  exact hgen

/-! ## §3–§4: the web identification. The parent H web is `tp ∈ [1, Lp]` at even sites and `tp ∈ [N, D + ε]` at odd
sites; the bottom collar has `t* ∈ [1 − Lp, 0]` (even) and `t* ∈ [1 − D, N]` (odd). Their intersection is `{N}` at odd
sites and empty at even sites, so the only free bottom root from the H web is `H_0` (odd `tp = N`). -/

theorem web_even_no_H (v : ℤ) (h2 : v ≤ 0) (hH : 1 ≤ v) : False := by
  omega

theorem web_odd_only_N (N v : ℤ) (h2 : v ≤ N) (hH : N ≤ v) : v = N := by
  omega

end FLatticePaper.W1Collar
