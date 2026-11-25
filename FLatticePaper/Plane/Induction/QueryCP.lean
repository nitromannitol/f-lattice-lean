import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Task w3, step 1(b)(C): the representative of a transport query lies in the conjugate's closed polygon (integer core).

Odd parent `N/D` with `1 ≤ N < D`; `b = D − N`, `r = D + N`, `T_p = D² + 2DN − N²`. The conjugate child is `b/r`, with
`L' = 2D`, `c' = 2N`, `T' = 2 T_p`. The representative of the query `Z x = (−x₂, x₁ − 1)` is `rep = (−x₂ + 2Nm, i)` where
`x₁ − 1 = 2Dm + i`, `0 ≤ i < 2D` (`rep = Z x − m V'`, `V' = (−2N, 2D)`). Its grades are
`t'(rep) = b·rep₁ − r·rep₂` and `s'(rep) = 2D·rep₁ + 2N·rep₂ = 2 t_p(x) − 2N`, and the key identity
`D · t'(rep) = D r + b t_p(x) − T_p (i + 1)`. -/

namespace FLatticePaper.QueryCP

/-- **The key identity** for the representative: `D · t'(rep) = D r + b t_p − T_p (i + 1)`. -/
theorem key_tprime (N D x1 x2 m i : ℤ) (hk : x1 - 1 = 2 * D * m + i) :
    D * ((D - N) * (-x2 + 2 * N * m) - (D + N) * i) =
      D * (D + N) + (D - N) * (N * x1 - D * x2) - (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1) := by
  linear_combination (-(D - N) * N) * hk

/-- **The grade identity:** `s'(rep) = 2 t_p(x) − 2N`. -/
theorem key_sprime (N D x1 x2 m i : ℤ) (hk : x1 - 1 = 2 * D * m + i) :
    2 * D * (-x2 + 2 * N * m) + 2 * N * i = 2 * (N * x1 - D * x2) - 2 * N := by
  linear_combination (-2 * N) * hk

/-- **Even window** (`x` odd, so the representative is even): `t'` and `s'` lie in the conjugate's even polygon window,
given `N ≤ t_p ≤ D` and `0 ≤ i < 2D`. -/
theorem even_window (N D tp i tt : ℤ) (hN : 1 ≤ N) (hND : N < D) (hi0 : 0 ≤ i) (hi1 : i < 2 * D)
    (htp0 : N ≤ tp) (htp1 : tp ≤ D) (hT : D * tt = D * (D + N) + (D - N) * tp - (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1)) :
    2 - 2 * (D ^ 2 + 2 * D * N - N ^ 2) ≤ tt ∧ tt ≤ 2 * D - 2 := by
  have hT0 : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have hTge : 2 * D ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have hb : 0 ≤ D - N := by omega
  have hDpos : 0 < D := by omega
  have hi1' : i + 1 ≤ 2 * D := by omega
  have hi1'' : 1 ≤ i + 1 := by omega
  have e1 : (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1) ≤ (D ^ 2 + 2 * D * N - N ^ 2) * (2 * D) :=
    mul_le_mul_of_nonneg_left hi1' hT0
  have e2 : (D ^ 2 + 2 * D * N - N ^ 2) ≤ (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1) := by
    have := mul_le_mul_of_nonneg_left hi1'' hT0
    linarith
  have e3 : (D - N) * tp ≤ (D - N) * D := mul_le_mul_of_nonneg_left htp1 hb
  have e4 : 0 ≤ (D - N) * tp := mul_nonneg hb (by omega)
  have e5 : 2 * D ≤ D * (D + N) := by nlinarith
  have hlo : D * (2 - 2 * (D ^ 2 + 2 * D * N - N ^ 2)) ≤ D * tt := by
    rw [hT]
    nlinarith
  have hhi : D * tt ≤ D * (2 * D - 2) := by
    rw [hT]
    nlinarith
  constructor
  · exact le_of_mul_le_mul_left hlo hDpos
  · exact le_of_mul_le_mul_left hhi hDpos

/-- **Odd window** (`x` even, so the representative is odd): `t'` and `s'` lie in the conjugate's odd polygon window,
given `1 ≤ t_p ≤ r` and `0 ≤ i < 2D`. -/
theorem odd_window (N D tp i tt : ℤ) (hN : 1 ≤ N) (hND : N < D) (hi0 : 0 ≤ i) (hi1 : i < 2 * D)
    (htp0 : 1 ≤ tp) (htp1 : tp ≤ D + N) (hT : D * tt = D * (D + N) + (D - N) * tp - (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1)) :
    (D - N) - 2 * (D ^ 2 + 2 * D * N - N ^ 2) ≤ tt ∧ tt ≤ D + N := by
  have hT0 : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have hb : 0 ≤ D - N := by omega
  have hDpos : 0 < D := by omega
  have hi1' : i + 1 ≤ 2 * D := by omega
  have hi1'' : 1 ≤ i + 1 := by omega
  have e1 : (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1) ≤ (D ^ 2 + 2 * D * N - N ^ 2) * (2 * D) :=
    mul_le_mul_of_nonneg_left hi1' hT0
  have e2 : (D ^ 2 + 2 * D * N - N ^ 2) ≤ (D ^ 2 + 2 * D * N - N ^ 2) * (i + 1) := by
    have := mul_le_mul_of_nonneg_left hi1'' hT0
    linarith
  have e3 : (D - N) * tp ≤ (D - N) * (D + N) := mul_le_mul_of_nonneg_left htp1 hb
  have e4 : 0 ≤ (D - N) * tp := mul_nonneg hb (by omega)
  have e5 : (D - N) * (D + N) ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have hlo : D * ((D - N) - 2 * (D ^ 2 + 2 * D * N - N ^ 2)) ≤ D * tt := by
    rw [hT]
    nlinarith
  have hhi : D * tt ≤ D * (D + N) := by
    rw [hT]
    nlinarith
  constructor
  · exact le_of_mul_le_mul_left hlo hDpos
  · exact le_of_mul_le_mul_left hhi hDpos

end FLatticePaper.QueryCP
