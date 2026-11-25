import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Task 72 / Q29, the arithmetic core of the raw V cut (`ANCESTRAL_PSI_V_CUT_PROOF.md` §§2–3).

The proof lifts each nonfinal child V root to an integer `b` and a residue `k` with `j = k + b r` (case (i)), `j = b r` (ii) and
`j = b r − 1` (iii), with `r = D + N`, and reads off `ψ⁻ = b + 1_{k>0}` (case (i)), `b` (cases (ii), (iii)). In every case this is
`ceil(j / r)`, and `Dminus(V_j) = −min(ceil(j/r), 2)` gives the cut list `0, (−1)^r, (−2)^(…)`.

This file proves only that integer arithmetic. The geometric inputs of §§1–3 (the earlier price identities, the classification of the
child V roots, the value `g_j = ψ⁻(v_j)`, and the final root) are not formalized here. -/

namespace FLatticePaper.ArcCut

/-- `⌈j / r⌉` for an integer numerator and a positive denominator. -/
def ceilDiv (j r : ℤ) : ℤ := (j + r - 1) / r

theorem ediv_shift_eq (r k : ℤ) (hr : 0 < r) (hk0 : 0 ≤ k) (hk : k < r) :
    (k + r - 1) / r = if k = 0 then 0 else 1 := by
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl]
    apply Int.ediv_eq_zero_of_lt <;> omega
  · rw [if_neg h0]
    have h1 : 1 ≤ (k + r - 1) / r := (Int.le_ediv_iff_mul_le hr).2 (by omega)
    have h2 : (k + r - 1) / r < 2 := (Int.ediv_lt_iff_lt_mul hr).2 (by omega)
    omega

/-- **The exact quotient lift:** for `j = k + b r` with `0 ≤ k < r`, `⌈j / r⌉ = b + 1_{k > 0}`. -/
theorem ceilDiv_lift (r b k : ℤ) (hr : 0 < r) (hk0 : 0 ≤ k) (hk : k < r) :
    ceilDiv (k + b * r) r = b + if k = 0 then 0 else 1 := by
  unfold ceilDiv
  have e : k + b * r + r - 1 = (k + r - 1) + b * r := by ring
  rw [e, Int.add_mul_ediv_right _ _ hr.ne', ediv_shift_eq r k hr hk0 hk]
  ring

/-- Case (ii): `j = b r` gives `b`. -/
theorem ceilDiv_mul (r b : ℤ) (hr : 0 < r) : ceilDiv (b * r) r = b := by
  have e : b * r = 0 + b * r := by ring
  rw [e, ceilDiv_lift r b 0 hr le_rfl hr]
  simp

/-- Case (iii): `j = b r − 1` gives `b`, provided `r ≥ 2`. -/
theorem ceilDiv_mul_sub_one (r b : ℤ) (hr : 2 ≤ r) : ceilDiv (b * r - 1) r = b := by
  have e : b * r - 1 = (r - 1) + (b - 1) * r := by ring
  rw [e, ceilDiv_lift r (b - 1) (r - 1) (by omega) (by omega) (by omega), if_neg (by omega)]
  ring

/-- The first nonfinal value: `⌈0 / r⌉ = 0`. -/
theorem ceilDiv_zero (r : ℤ) (hr : 0 < r) : ceilDiv 0 r = 0 := by
  unfold ceilDiv
  rw [ediv_shift_eq r 0 hr le_rfl hr]
  simp

/-- The first `r` nonzero values: `⌈j / r⌉ = 1` for `1 ≤ j ≤ r`. -/
theorem ceilDiv_one (r j : ℤ) (hr : 0 < r) (h1 : 1 ≤ j) (h2 : j ≤ r) : ceilDiv j r = 1 := by
  unfold ceilDiv
  have hlt : (j + r - 1) / r < 2 := (Int.ediv_lt_iff_lt_mul hr).2 (by omega)
  have hge : 1 ≤ (j + r - 1) / r := (Int.le_ediv_iff_mul_le hr).2 (by omega)
  omega

/-- Every later value is at least two: `⌈j / r⌉ ≥ 2` for `j ≥ r + 1`. -/
theorem ceilDiv_two_le (r j : ℤ) (hr : 0 < r) (h : r + 1 ≤ j) : 2 ≤ ceilDiv j r := by
  unfold ceilDiv
  exact (Int.le_ediv_iff_mul_le hr).2 (by omega)

/-- The cut value `−min(⌈j / r⌉, 2)` is `0` at the first root, `−1` on the next `r` roots, and `−2` on every later root. -/
theorem cut_value (r j : ℤ) (hr : 0 < r) (hj : 0 ≤ j) :
    min (ceilDiv j r) 2 = if j = 0 then 0 else if j ≤ r then 1 else 2 := by
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl, ceilDiv_zero r hr]
    simp
  · rw [if_neg h0]
    by_cases hr' : j ≤ r
    · rw [if_pos hr', ceilDiv_one r j hr (by omega) hr']
      simp
    · rw [if_neg hr']
      have := ceilDiv_two_le r j hr (by omega)
      exact min_eq_right this

end FLatticePaper.ArcCut
