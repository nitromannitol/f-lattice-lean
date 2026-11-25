import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Task w3, step 1(b)(iii)–(iv): the two exclusions in the transport classification (integer core).

(iii) Phase one, `t_p = D + 1` at an odd free H point forces `t = d` and `u = L − 1`, hence the abscissa `w₁ = d` (the point `H_{d−1}`,
which is `j = 0`). So for `j ≥ 1` the odd query has `t_p ≤ D`.
(iv) Phase one, the origin-type query `(2Dm + 1, 2Nm)` with odd `t ∈ [n, d]` forces `m = 0`, since `t = n − 2m`. -/

namespace FLatticePaper.QueryClass

/-- **(iii) The phase-one odd bound.** With `L = d + n`, `t = n w₁ − d w₂`, `u = w₁ + w₂`, `(D+N) d = D L + 1`,
`L t_p = (D+N) t + u`, `t ≤ d`, `u ≤ L − 1`, `t_p ≤ D + 1` and `w₁ ≠ d`: `t_p ≤ D`. -/
theorem tp_le_D_of_w1_ne (D N n d w1 w2 tp : ℤ) (hD : 0 < D) (hN : 0 ≤ N) (hL : 0 < d + n)
    (hrd : (D + N) * d = D * (d + n) + 1)
    (key : (d + n) * tp = (D + N) * (n * w1 - d * w2) + (w1 + w2))
    (ht : n * w1 - d * w2 ≤ d) (hu : w1 + w2 ≤ d + n - 1) (htp : tp ≤ D + 1) (hw : w1 ≠ d) :
    tp ≤ D := by
  by_contra hc
  have htpD : tp = D + 1 := by omega
  subst htpD
  -- step 1: t = d
  have hteq : n * w1 - d * w2 = d := by
    by_contra hne
    have hlt : n * w1 - d * w2 ≤ d - 1 := by omega
    have hr : 0 ≤ D + N := by omega
    have h1 : (D + N) * (n * w1 - d * w2) ≤ (D + N) * (d - 1) := mul_le_mul_of_nonneg_left hlt hr
    nlinarith
  -- step 2: u = L − 1
  have hu1 : w1 + w2 = d + n - 1 := by
    rw [hteq] at key
    linarith
  -- step 3: L w1 = t + d u = d L, so w1 = d
  have hid : (d + n) * w1 = (n * w1 - d * w2) + d * (w1 + w2) := by ring
  rw [hteq, hu1] at hid
  have hfin : (d + n) * (w1 - d) = 0 := by linarith
  rcases mul_eq_zero.mp hfin with h0 | h0
  · omega
  · exact hw (by linarith)

/-- **(iv) The origin-type query in phase one.** If `x = (2Dm + 1, 2Nm)` (so `t = n − 2m` for `ε = +1`) and `t ≥ n`, then `m = 0`
(with `m ≥ 0` from `x₁ ≥ 1`). -/
theorem origin_m_zero (D N n d m : ℤ) (hm : 0 ≤ m) (hε : N * d - D * n = 1)
    (ht : n ≤ n * (2 * D * m + 1) - d * (2 * N * m)) : m = 0 := by
  have e : n * (2 * D * m + 1) - d * (2 * N * m) = n - 2 * m := by
    linear_combination (-2 * m) * hε
  rw [e] at ht
  omega

end FLatticePaper.QueryClass
