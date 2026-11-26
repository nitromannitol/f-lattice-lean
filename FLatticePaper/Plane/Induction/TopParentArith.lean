import Mathlib.Tactic

/-! # The parent query bounds on the top collar (integer arithmetic, audit section 1)

Notation: `N/D` the odd parent (`N = odd.num`, `D = odd.den`), `n/d` the child, `L = d + n`, `c = d − n`,
`T = d² + 2dn − n²`, `C = D L + N c`, and `ε = N d − D n = ±1`. The parent grade `P = N x₁ − D x₂` of a site `y` satisfies
`T P(y) = C t(y) + ε s(y)` (`periodDenominator_parentTGrade`), and the parent query of `y` is `P(y) − W`, `W = (1 + ε)/2`.

The four theorems below give the window `[1 − Lp, 2Lp − 1]` (even sites) or `[1 − D, N + 2D − 1]` (odd sites) for `P − W`,
from the top collar bounds of `t(y)`, `s(y)`. The identities used: `C L = Lp T − 2 ε n`, `C n = N T − ε L`, `C d = D T + ε c`,
and `T = 2C + (d − 2D) L + (n − 2N) c`. -/

namespace FLatticePaper.TopParentArith

/-- The even top sites, `ε = 1`: the query `P − 1` lies in `[1 − (N + D), 2 (N + D) − 1]`. -/
theorem even_plus (N D n d P t s : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hdq : 2 * D ≤ d) (hnq : 2 * N ≤ n) (hε : 1 = N * d - D * n)
    (hP : (d ^ 2 + 2 * d * n - n ^ 2) * P = (D * (d + n) + N * (d - n)) * t + 1 * s)
    (ht1 : d + n - 2 < t) (ht2 : t ≤ 2 * (d + n) - 2) (hs1 : 2 * n < s)
    (hs2 : s < d ^ 2 + 2 * d * n - n ^ 2) :
    1 - (N + D) ≤ P - 1 ∧ P - 1 ≤ 2 * (N + D) - 1 := by
  have hT0 : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC0 : 0 ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hTC : 2 * (D * (d + n) + N * (d - n)) ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hdq) (show (0:ℤ) ≤ d + n by omega),
      mul_nonneg (sub_nonneg.2 hnq) (show (0:ℤ) ≤ d - n by omega)]
  have hCL : (D * (d + n) + N * (d - n)) * (d + n) = (D + N) * (d ^ 2 + 2 * d * n - n ^ 2) - 2 * n := by
    linear_combination (2 * n) * hε
  have h1 : (D * (d + n) + N * (d - n)) * t ≤ (D * (d + n) + N * (d - n)) * (2 * (d + n) - 2) :=
    mul_le_mul_of_nonneg_left ht2 hC0
  have h2 : (D * (d + n) + N * (d - n)) * (d + n - 2) ≤ (D * (d + n) + N * (d - n)) * t :=
    mul_le_mul_of_nonneg_left ht1.le hC0
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * (P - 1) < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * (N + D)) := by
    nlinarith
  have hlow : 1 - (N + D) ≤ P - 1 := by
    by_contra hc
    have hle : P - 1 ≤ -(N + D) := by omega
    have hm := mul_le_mul_of_nonneg_left hle hT0.le
    have hND : 2 * (d ^ 2 + 2 * d * n - n ^ 2) ≤ (N + D) * (d ^ 2 + 2 * d * n - n ^ 2) :=
      mul_le_mul_of_nonneg_right (by omega) hT0.le
    nlinarith
  refine ⟨hlow, ?_⟩
  have := lt_of_mul_lt_mul_left hup hT0.le
  omega

/-- The even top sites, `ε = −1`: the query `P` lies in `[1 − (N + D), 2 (N + D) − 1]`. -/
theorem even_minus (N D n d P t s : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hdq : 2 * D ≤ d) (hnq : 2 * N ≤ n) (hε : -1 = N * d - D * n)
    (hP : (d ^ 2 + 2 * d * n - n ^ 2) * P = (D * (d + n) + N * (d - n)) * t + (-1) * s)
    (ht1 : d + n - 2 < t) (ht2 : t ≤ 2 * (d + n) - 2) (hs1 : 2 * n < s)
    (hs2 : s < d ^ 2 + 2 * d * n - n ^ 2) :
    1 - (N + D) ≤ P ∧ P ≤ 2 * (N + D) - 1 := by
  have hT0 : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC0 : 0 ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hCgt : n < D * (d + n) + N * (d - n) := by nlinarith
  have hTC : 2 * (D * (d + n) + N * (d - n)) ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hdq) (show (0:ℤ) ≤ d + n by omega),
      mul_nonneg (sub_nonneg.2 hnq) (show (0:ℤ) ≤ d - n by omega)]
  have hCL : (D * (d + n) + N * (d - n)) * (d + n) = (D + N) * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n := by
    linear_combination (2 * n) * hε
  have h1 : (D * (d + n) + N * (d - n)) * t ≤ (D * (d + n) + N * (d - n)) * (2 * (d + n) - 2) :=
    mul_le_mul_of_nonneg_left ht2 hC0
  have h2 : (D * (d + n) + N * (d - n)) * (d + n - 2) ≤ (D * (d + n) + N * (d - n)) * t :=
    mul_le_mul_of_nonneg_left ht1.le hC0
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * P < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * (N + D)) := by
    nlinarith
  have hlow : 1 - (N + D) ≤ P := by
    by_contra hc
    have hle : P ≤ -(N + D) := by omega
    have hm := mul_le_mul_of_nonneg_left hle hT0.le
    have hND : 2 * (d ^ 2 + 2 * d * n - n ^ 2) ≤ (N + D) * (d ^ 2 + 2 * d * n - n ^ 2) :=
      mul_le_mul_of_nonneg_right (by omega) hT0.le
    nlinarith
  refine ⟨hlow, ?_⟩
  have := lt_of_mul_lt_mul_left hup hT0.le
  omega

/-- The odd top sites, `ε = 1`: the query `P − 1` lies in `[1 − D, N + 2D − 1]`. -/
theorem odd_plus (N D n d P t s : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hdq : 2 * D ≤ d) (hnq : 2 * N ≤ n) (hε : 1 = N * d - D * n)
    (hP : (d ^ 2 + 2 * d * n - n ^ 2) * P = (D * (d + n) + N * (d - n)) * t + 1 * s)
    (ht1 : d < t) (ht2 : t ≤ n + 2 * d - 2) (hs1 : d + n - 2 < s)
    (hs2 : s < d ^ 2 + 2 * d * n - n ^ 2 + (2 - (d - n))) :
    1 - D ≤ P - 1 ∧ P - 1 ≤ N + 2 * D - 1 := by
  have hT0 : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC0 : 0 ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hTC : 2 * (D * (d + n) + N * (d - n)) ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hdq) (show (0:ℤ) ≤ d + n by omega),
      mul_nonneg (sub_nonneg.2 hnq) (show (0:ℤ) ≤ d - n by omega)]
  -- `C n = N T − ε L` and `C d = D T + ε c` with `ε = 1`
  have hCn : (D * (d + n) + N * (d - n)) * n = N * (d ^ 2 + 2 * d * n - n ^ 2) - (d + n) := by
    linear_combination (d + n) * hε
  have hCd : (D * (d + n) + N * (d - n)) * d = D * (d ^ 2 + 2 * d * n - n ^ 2) + (d - n) := by
    linear_combination (-(d - n)) * hε
  have h1 : (D * (d + n) + N * (d - n)) * t ≤ (D * (d + n) + N * (d - n)) * (n + 2 * d - 2) :=
    mul_le_mul_of_nonneg_left ht2 hC0
  have h2 : (D * (d + n) + N * (d - n)) * d ≤ (D * (d + n) + N * (d - n)) * t :=
    mul_le_mul_of_nonneg_left ht1.le hC0
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * (P - 1) < (d ^ 2 + 2 * d * n - n ^ 2) * (N + 2 * D) := by
    nlinarith
  have hlow : 1 - D ≤ P - 1 := by
    by_contra hc
    have hle : P - 1 ≤ -D := by omega
    have hm := mul_le_mul_of_nonneg_left hle hT0.le
    have hDT : 0 ≤ (D - 1) * (d ^ 2 + 2 * d * n - n ^ 2) :=
      mul_nonneg (by omega) hT0.le
    have hCd0 : 0 ≤ (D * (d + n) + N * (d - n)) * d := mul_nonneg hC0 (by omega)
    nlinarith
  refine ⟨hlow, ?_⟩
  have := lt_of_mul_lt_mul_left hup hT0.le
  omega

/-- The odd top sites, `ε = −1`: the query `P` lies in `[1 − D, N + 2D − 1]`. -/
theorem odd_minus (N D n d P t s : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD2 : 2 ≤ D) (hN0 : 0 ≤ N)
    (hdq : 2 * D ≤ d) (hnq : 2 * N ≤ n) (hε : -1 = N * d - D * n)
    (hP : (d ^ 2 + 2 * d * n - n ^ 2) * P = (D * (d + n) + N * (d - n)) * t + (-1) * s)
    (ht1 : d < t) (ht2 : t ≤ n + 2 * d - 2) (hs1 : d + n - 2 < s)
    (hs2 : s < d ^ 2 + 2 * d * n - n ^ 2 + (2 - (d - n))) :
    1 - D ≤ P ∧ P ≤ N + 2 * D - 1 := by
  have hT0 : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hT2 : 2 ≤ d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hC0 : 0 ≤ D * (d + n) + N * (d - n) := by nlinarith
  have hTC : 2 * (D * (d + n) + N * (d - n)) ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hdq) (show (0:ℤ) ≤ d + n by omega),
      mul_nonneg (sub_nonneg.2 hnq) (show (0:ℤ) ≤ d - n by omega)]
  -- `C n = N T − ε L`, `C d = D T + ε c` with `ε = −1`
  have hCn : (D * (d + n) + N * (d - n)) * n = N * (d ^ 2 + 2 * d * n - n ^ 2) + (d + n) := by
    linear_combination (d + n) * hε
  have hCd : (D * (d + n) + N * (d - n)) * d = D * (d ^ 2 + 2 * d * n - n ^ 2) - (d - n) := by
    linear_combination (-(d - n)) * hε
  have h1 : (D * (d + n) + N * (d - n)) * t ≤ (D * (d + n) + N * (d - n)) * (n + 2 * d - 2) :=
    mul_le_mul_of_nonneg_left ht2 hC0
  have h2 : (D * (d + n) + N * (d - n)) * d ≤ (D * (d + n) + N * (d - n)) * t :=
    mul_le_mul_of_nonneg_left ht1.le hC0
  have hup : (d ^ 2 + 2 * d * n - n ^ 2) * P < (d ^ 2 + 2 * d * n - n ^ 2) * (N + 2 * D) := by
    nlinarith
  have hlow : 1 - D ≤ P := by
    by_contra hc
    have hle : P ≤ -D := by omega
    have hm := mul_le_mul_of_nonneg_left hle hT0.le
    have hDT : 0 ≤ (D - 2) * (d ^ 2 + 2 * d * n - n ^ 2) := mul_nonneg (by omega) hT0.le
    nlinarith
  refine ⟨hlow, ?_⟩
  have := lt_of_mul_lt_mul_left hup hT0.le
  omega

end FLatticePaper.TopParentArith
