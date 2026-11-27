import Mathlib

/-! # The left face: the pure algebra of the parent window

Child `(n, d)` (odd, `3 ≤ n < d`), parent `(N, D)` with `N d − D n = 1` (`ε = 1`), `L = d + n`, `m = d − n`,
`T = d² + 2dn − n²` (child period), `C = D L + N m`, and `Tp = D² + 2DN − N²` (parent period).

The identities are `n C + L = N T`, `(D + N) T − L C = 2n`, and `N (N-polynomial) = G` for the odd upper bound. -/

namespace FLatticePaper.LeftPure

theorem id_I1 (N D n d : ℤ) (h : N * d - D * n = 1) :
    n * (D * (d + n) + N * (d - n)) + (d + n) = N * (d * d + 2 * d * n - n * n) := by
  linear_combination (-(d + n)) * h

theorem id_I2 (N D n d : ℤ) (h : N * d - D * n = 1) :
    (D + N) * (d * d + 2 * d * n - n * n) - (d + n) * (D * (d + n) + N * (d - n)) = 2 * n := by
  linear_combination (2 * n) * h

theorem id_odd_upper (N D n d : ℤ) (h : N * d - D * n = 1) :
    N * ((3 * D + N) * (d * d + 2 * d * n - n * n) - (D * (d + n) + N * (d - n)) * (3 * d + n - 2)
      - 2 * (n - 2)) =
      2 * n * (D * D + 2 * D * N - N * N) + 2 * n * (N - D) + 2 * (N + D) + 4 * N - 2 := by
  linear_combination (-2 * (-D + N * d - 2 * N * n - N + 1)) * h

/-- **The even parent window.** If `2n + 2 ≤ s`, `L − T ≤ t ≤ 0`, `s ≤ 2L` and `T v = C s + 2 t`, then `2N ≤ v ≤ 2D + 2N − 2`
for an even `v`. -/
theorem v_even_window (N D n d t s v : ℤ) (h : N * d - D * n = 1) (hn3 : 3 ≤ n) (hnd : n < d)
    (hN : 0 < N) (hND : N < D)
    (hTv : (d * d + 2 * d * n - n * n) * v = (D * (d + n) + N * (d - n)) * s + 2 * t)
    (ht1 : (d + n) - (d * d + 2 * d * n - n * n) ≤ t) (ht2 : t ≤ 0)
    (hs1 : 2 * n + 2 ≤ s) (hs2 : s ≤ 2 * (d + n)) (hpar : v % 2 = 0) :
    2 * N ≤ v ∧ v ≤ 2 * D + 2 * N - 2 := by
  have hI1 := id_I1 N D n d h
  have hI2 := id_I2 N D n d h
  have hT : 0 < d * d + 2 * d * n - n * n := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have hCs1 : (D * (d + n) + N * (d - n)) * (2 * n + 2) ≤ (D * (d + n) + N * (d - n)) * s :=
    mul_le_mul_of_nonneg_left hs1 hC.le
  have hCs2 : (D * (d + n) + N * (d - n)) * s ≤ (D * (d + n) + N * (d - n)) * (2 * (d + n)) :=
    mul_le_mul_of_nonneg_left hs2 hC.le
  constructor
  · have hlow : 0 < (d * d + 2 * d * n - n * n) * (v - 2 * N + 2) := by nlinarith
    have hpos : 0 < v - 2 * N + 2 := pos_of_mul_pos_right hlow hT.le
    omega
  · have hup : (d * d + 2 * d * n - n * n) * v < (d * d + 2 * d * n - n * n) * (2 * D + 2 * N) := by nlinarith
    have hv : v < 2 * D + 2 * N := lt_of_mul_lt_mul_left hup hT.le
    omega

/-- **The odd parent window.** If `L ≤ s`, `d − T + 2 ≤ t ≤ n − 2`, `s ≤ 3d + n − 2` and `T v = C s + 2 t`, then
`D + N ≤ v ≤ 3D + N − 2` for an odd `v` (with `D + N` odd). -/
theorem v_odd_window (N D n d t s v : ℤ) (h : N * d - D * n = 1) (hn3 : 3 ≤ n) (hnd : n < d)
    (hN : 0 < N) (hND : N < D) (hSodd : (D + N) % 2 = 1)
    (hTv : (d * d + 2 * d * n - n * n) * v = (D * (d + n) + N * (d - n)) * s + 2 * t)
    (ht1 : d - (d * d + 2 * d * n - n * n) + 2 ≤ t) (ht2 : t ≤ n - 2)
    (hs1 : d + n ≤ s) (hs2 : s ≤ 3 * d + n - 2) (hpar : v % 2 = 1) :
    D + N ≤ v ∧ v ≤ 3 * D + N - 2 := by
  have hI1 := id_I1 N D n d h
  have hI2 := id_I2 N D n d h
  have hF := id_odd_upper N D n d h
  have hT : 0 < d * d + 2 * d * n - n * n := by nlinarith
  have hC : 0 < D * (d + n) + N * (d - n) := by nlinarith
  have hCs1 : (D * (d + n) + N * (d - n)) * (d + n) ≤ (D * (d + n) + N * (d - n)) * s :=
    mul_le_mul_of_nonneg_left hs1 hC.le
  have hCs2 : (D * (d + n) + N * (d - n)) * s ≤ (D * (d + n) + N * (d - n)) * (3 * d + n - 2) :=
    mul_le_mul_of_nonneg_left hs2 hC.le
  have hCt1 : (D * (d + n) + N * (d - n)) * (d - (d * d + 2 * d * n - n * n) + 2) ≤ (D * (d + n) + N * (d - n)) * t :=
    mul_le_mul_of_nonneg_left ht1 hC.le
  have hCt2 : (D * (d + n) + N * (d - n)) * t ≤ (D * (d + n) + N * (d - n)) * (n - 2) :=
    mul_le_mul_of_nonneg_left ht2 hC.le
  have hGpos : 0 < 2 * n * (D * D + 2 * D * N - N * N) + 2 * n * (N - D) + 2 * (N + D) + 4 * N - 2 := by
    nlinarith
  constructor
  · have hlow : 0 < (d * d + 2 * d * n - n * n) * (v - (D + N) + 2) := by nlinarith
    have hpos : 0 < v - (D + N) + 2 := pos_of_mul_pos_right hlow hT.le
    omega
  · have hF0 : 0 < (3 * D + N) * (d * d + 2 * d * n - n * n)
        - (D * (d + n) + N * (d - n)) * (3 * d + n - 2) - 2 * (n - 2) := by
      have hNpos : 0 < N := hN
      have : N * ((3 * D + N) * (d * d + 2 * d * n - n * n)
          - (D * (d + n) + N * (d - n)) * (3 * d + n - 2) - 2 * (n - 2)) > 0 := by
        rw [hF]; exact hGpos
      exact pos_of_mul_pos_right this hNpos.le
    have hup : (d * d + 2 * d * n - n * n) * v < (d * d + 2 * d * n - n * n) * (3 * D + N) := by nlinarith
    have hv : v < 3 * D + N := lt_of_mul_lt_mul_left hup hT.le
    omega

end FLatticePaper.LeftPure
