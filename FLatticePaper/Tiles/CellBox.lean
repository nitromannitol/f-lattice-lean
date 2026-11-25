import FLatticePaper.Tiles.CellIntervals

/-! Task Q25 (completeness of the seam), the box of the cell tile (`fixes/Q25.md`, "The cell boundary").

Let `T = D² + 2DN − N²`, `C = D − N`, `L = D + N`. The identities `T x = C t + D s` and `T y = N s − L t` (with `t = N x − D y`,
`s = L x + C y`) turn the four-test bounds (1) into `1 − C ≤ x ≤ μD − 1` and `0 ≤ y ≤ μN + L − 2`. The only numerical inputs are
`C k < D (2C + λ)`, `N λ − L k + T > 0` and `L k + T < 2NC + Nλ + 2LD` at the grade `k` and slope bound `λ` of the cell, and these hold
for the even and the odd constants (`box_facts_even`, `box_facts_odd`). -/

namespace FLatticePaper.Tiles.CellBox

open FLatticePaper.Tiles.CellIntervals

/-- The box of the cell tile from the four-test bounds at a cell with grade bound `k` and slope bound `l`. -/
theorem box_core (N D μ x y k l : ℤ) (hN : 1 ≤ N) (hND : N < D) (_hμ1 : 1 ≤ μ) (_hμ2 : μ ≤ 2)
    (hA : 2 * D - (D ^ 2 + 2 * D * N - N ^ 2) - k ≤ N * x - D * y) (hB : N * x - D * y ≤ k)
    (hC : l ≤ (D + N) * x + (D - N) * y)
    (hD : (D + N) * x + (D - N) * y ≤ μ * (D ^ 2 + 2 * D * N - N ^ 2) - 2 * (D - N) - l)
    (N1 : (D - N) * k < D * (2 * (D - N) + l))
    (N2 : N * l - (D + N) * k + (D ^ 2 + 2 * D * N - N ^ 2) > 0)
    (_N3 : (D + N) * k + (D ^ 2 + 2 * D * N - N ^ 2) < 2 * N * (D - N) + N * l + 2 * (D + N) * D) :
    1 - (D - N) ≤ x ∧ x ≤ μ * D - 1 ∧ 0 ≤ y ∧ y ≤ μ * N + (D + N) - 2 := by
  have hT : 0 < D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have idX : (D ^ 2 + 2 * D * N - N ^ 2) * x =
      (D - N) * (N * x - D * y) + D * ((D + N) * x + (D - N) * y) := by ring
  have idY : (D ^ 2 + 2 * D * N - N ^ 2) * y =
      N * ((D + N) * x + (D - N) * y) - (D + N) * (N * x - D * y) := by ring
  have hC0 : (0 : ℤ) ≤ D - N := by omega
  have hD0 : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  have hL0 : (0 : ℤ) ≤ D + N := by omega
  have xu : (D ^ 2 + 2 * D * N - N ^ 2) * x < (D ^ 2 + 2 * D * N - N ^ 2) * (μ * D) := by
    nlinarith [mul_le_mul_of_nonneg_left hB hC0, mul_le_mul_of_nonneg_left hD hD0]
  have xl : (D ^ 2 + 2 * D * N - N ^ 2) * (-(D - N)) < (D ^ 2 + 2 * D * N - N ^ 2) * x := by
    nlinarith [mul_le_mul_of_nonneg_left hA hC0, mul_le_mul_of_nonneg_left hC hD0]
  have yl : (D ^ 2 + 2 * D * N - N ^ 2) * (-1) < (D ^ 2 + 2 * D * N - N ^ 2) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hC hN0, mul_le_mul_of_nonneg_left hB hL0]
  have yu : (D ^ 2 + 2 * D * N - N ^ 2) * y <
      (D ^ 2 + 2 * D * N - N ^ 2) * (μ * N + (D + N) - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hD hN0, mul_le_mul_of_nonneg_left hA hL0]
  have xu' := lt_of_mul_lt_mul_left xu hT.le
  have xl' := lt_of_mul_lt_mul_left xl hT.le
  have yl' := lt_of_mul_lt_mul_left yl hT.le
  have yu' := lt_of_mul_lt_mul_left yu hT.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : -(D - N) < x := xl'
    omega
  · omega
  · have : -1 < y := yl'
    omega
  · have : y < μ * N + (D + N) - 1 := yu'
    omega

/-- The numerical facts at the even constants: grade `C`, slope bound `0`. -/
theorem box_facts_even (N D : ℤ) (hN : 1 ≤ N) (hND : N < D) :
    (D - N) * (D - N) < D * (2 * (D - N) + 0) ∧
      N * 0 - (D + N) * (D - N) + (D ^ 2 + 2 * D * N - N ^ 2) > 0 ∧
        (D + N) * (D - N) + (D ^ 2 + 2 * D * N - N ^ 2) < 2 * N * (D - N) + N * 0 + 2 * (D + N) * D := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- The numerical facts at the odd constants: grade `K1 = max (D − 2N) N`, slope bound `Λ1 = min (D − N) (3N − D)`. -/
theorem box_facts_odd (N D : ℤ) (hN : 1 ≤ N) (hND : N < D) :
    (D - N) * max (D - 2 * N) N < D * (2 * (D - N) + min (D - N) (3 * N - D)) ∧
      N * min (D - N) (3 * N - D) - (D + N) * max (D - 2 * N) N + (D ^ 2 + 2 * D * N - N ^ 2) > 0 ∧
        (D + N) * max (D - 2 * N) N + (D ^ 2 + 2 * D * N - N ^ 2) <
          2 * N * (D - N) + N * min (D - N) (3 * N - D) + 2 * (D + N) * D := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [max_def, min_def] <;> split_ifs <;> nlinarith

end FLatticePaper.Tiles.CellBox
