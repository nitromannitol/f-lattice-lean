import FLatticePaper.Plane.Induction.LeftVGrade
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.ArcRanges

/-! # The V-web bounds for a free V point at `ε = −1` (the right and up arcs)

For `ε = −1` (child `(n, d)` over odd `(N, D)` with `N d − D n = −1`, even parent `(P, Q)` with `N Q − P D = −1`, `n = 2N + P`,
`d = 2D + Q`), the integer identities are, with `T` the child period, `T_q` the parent's:

* `T b = C s − 2t`, `n b = N s + m`, `n C = N T + L`, `(N + D) b − 2N a = T_q m`;
* even `z ≠ vLast`: `s ∈ [0, 2n]`, `t ∈ [2L − T, −L]`, so `1 ≤ b < 2N + 2`, and `b` is even: `0 ≤ b ≤ 2N`;
* odd `z`: `s ∈ [2 − (d − n), L − 2]`, `t ∈ [L + d − T, −d]`, so `N − D + 2 ≤ b ≤ N + D` (`b` odd);
* odd `z` with `b = N + D`: `2N (a − N) = −T_q (m − 1)` and `m − 1 = 2N k`, so `a − N + k T_q = 0`.

`vLast` is excluded from the even bound: there `b = 2N + 2` (the right-arc exception, `EndpointBlack`). -/

namespace FLatticePaper.LeftVNegProof

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.LeftVGrade

/-- `T b = C s − 2 t` (`ε = −1`). -/
theorem id_Tb_neg (N D n d z1 z2 : ℤ) (hε : N * d - D * n = -1) :
    (d ^ 2 + 2 * d * n - n ^ 2) * ((D + N) * z1 + (D - N) * z2) =
      (D * (d + n) + N * (d - n)) * ((d + n) * z1 + (d - n) * z2) - 2 * (n * z1 - d * z2) := by
  linear_combination (2 * (n * z1 - d * z2)) * hε

/-- `n b = N s + m` (`ε = −1`). -/
theorem id_nb_neg (N D n d z1 z2 : ℤ) (hε : N * d - D * n = -1) :
    n * ((D + N) * z1 + (D - N) * z2) = N * ((d + n) * z1 + (d - n) * z2) + (z1 + z2) := by
  linear_combination (-(z1 + z2)) * hε

/-- `n C = N T + L` (`ε = −1`). -/
theorem id_nC_neg (N D n d : ℤ) (hε : N * d - D * n = -1) :
    n * (D * (d + n) + N * (d - n)) = N * (d ^ 2 + 2 * d * n - n ^ 2) + (d + n) := by
  linear_combination (-d - n) * hε

/-- The lower key (`ε = −1`): `n · X = T (2N + 1) + L (2 − c) + 2nd`, `X = C (2 − c) + 2d − (N − D) T`. -/
theorem key_lower_neg (N D n d : ℤ) (hε : N * d - D * n = -1) :
    n * ((D * (d + n) + N * (d - n)) * (2 - (d - n)) + 2 * d - (N - D) * (d ^ 2 + 2 * d * n - n ^ 2)) =
      (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) + (d + n) * (2 - (d - n)) + 2 * n * d := by
  linear_combination (-2 * (d * n + d + n)) * hε

/-- The upper key (`ε = −1`): `n · Z = T (2N + 1) − L (L − 2) + 2nL + 2nd`, `Z = (N + D) T − C (L − 2) + 2L + 2d`. -/
theorem key_upper_neg (N D n d : ℤ) (hε : N * d - D * n = -1) :
    n * ((N + D) * (d ^ 2 + 2 * d * n - n ^ 2) - (D * (d + n) + N * (d - n)) * ((d + n) - 2) + 2 * (d + n) + 2 * d) =
      (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) - (d + n) * ((d + n) - 2) + 2 * n * (d + n) + 2 * n * d := by
  linear_combination (-2 * (d - n ^ 2 + n)) * hε

/-- The parent identity `(N + D) b − 2 N a = T_q (z₁ + z₂)` (no relation needed). -/
theorem id_ab_neg (N D z1 z2 : ℤ) :
    (N + D) * ((D + N) * z1 + (D - N) * z2) - 2 * N * (N * z1 - D * z2) =
      (D ^ 2 + 2 * D * N - N ^ 2) * (z1 + z2) := by
  ring

/-- **The even bound (`ε = −1`).** For `s ∈ [0, 2n]`, `t ∈ [2L − T, −L]`: `0 ≤ b ≤ 2N` (`b` even). -/
theorem core_even_neg {N D n d z1 z2 b : ℤ} (hN : 0 < N) (hND : N < D) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hε : N * d - D * n = -1) (hDN : (D + N) % 2 = 1) (hpar : (z1 + z2) % 2 = 0)
    (hb : b = (D + N) * z1 + (D - N) * z2)
    (hs0 : 0 ≤ (d + n) * z1 + (d - n) * z2) (hs1 : (d + n) * z1 + (d - n) * z2 ≤ 2 * n)
    (ht0 : 2 * (d + n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * z1 - d * z2)
    (ht1 : n * z1 - d * z2 ≤ -(d + n)) :
    0 ≤ b ∧ b ≤ 2 * N := by
  have hdn : n < d := by omega
  have hTc : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by
    have h1 : n * n < d * d := mul_self_lt_mul_self (by omega) hdn
    have h2 : 0 < d * n := mul_pos (by omega) (by omega)
    nlinarith [h1, h2]
  have hC : 0 < D * (d + n) + N * (d - n) := by
    have h1 := mul_pos (show (0 : ℤ) < D by omega) (show (0 : ℤ) < d + n by omega)
    have h2 := mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ d - n by omega)
    linarith
  have hid := id_Tb_neg N D n d z1 z2 hε
  rw [← hb] at hid
  have hnC := id_nC_neg N D n d hε
  have hup1 := mul_le_mul_of_nonneg_left hs1 hC.le
  have hlo1 := mul_le_mul_of_nonneg_left hs0 hC.le
  -- lower: `T b ≥ 2 L > 0`
  have hlo : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * b := by
    linarith
  have hbpos : 0 < b := pos_of_mul_pos_right hlo hTc.le
  -- upper: `T b ≤ 2 (N + 1) T − 2 L < 2 (N + 1) T`
  have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * b < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 2) := by
    linarith
  have hbup : b < 2 * N + 2 := lt_of_mul_lt_mul_left hlt hTc.le
  -- parity: `b ≡ z1 + z2 (mod 2)`
  obtain ⟨α, hα⟩ : ∃ α : ℤ, D + N = 2 * α + 1 := ⟨(D + N - 1) / 2, by omega⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, D - N = 2 * β + 1 := ⟨(D - N - 1) / 2, by omega⟩
  have bpar : b = 2 * (α * z1 + β * z2) + (z1 + z2) := by
    rw [hb, hα, hβ]
    ring
  generalize α * z1 + β * z2 = X at bpar
  constructor <;> omega

/-- **The odd bounds (`ε = −1`).** For `s ∈ [2 − (d − n), L − 2]`, `t ∈ [L + d − T, −d]`:
`N − D + 2 ≤ b ≤ N + D`, and `b` is odd. -/
theorem core_odd_neg {N D n d z1 z2 b : ℤ} (hN : 0 < N) (hND : N < D) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hε : N * d - D * n = -1) (hDN : (D + N) % 2 = 1) (hodd : (z1 + z2) % 2 = 1)
    (hb : b = (D + N) * z1 + (D - N) * z2)
    (hs0 : 2 - (d - n) ≤ (d + n) * z1 + (d - n) * z2) (hs1 : (d + n) * z1 + (d - n) * z2 ≤ (d + n) - 2)
    (ht0 : (d + n) + d - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * z1 - d * z2)
    (ht1 : n * z1 - d * z2 ≤ -d) :
    N - D + 2 ≤ b ∧ b ≤ N + D ∧ b % 2 = 1 := by
  have hdn : n < d := by omega
  have hTc : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by
    have h1 : n * n < d * d := mul_self_lt_mul_self (by omega) hdn
    have h2 : 0 < d * n := mul_pos (by omega) (by omega)
    nlinarith [h1, h2]
  have hC : 0 < D * (d + n) + N * (d - n) := by
    have h1 := mul_pos (show (0 : ℤ) < D by omega) (show (0 : ℤ) < d + n by omega)
    have h2 := mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ d - n by omega)
    linarith
  have hid := id_Tb_neg N D n d z1 z2 hε
  rw [← hb] at hid
  obtain ⟨α, hα⟩ : ∃ α : ℤ, D + N = 2 * α + 1 := ⟨(D + N - 1) / 2, by omega⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, D - N = 2 * β + 1 := ⟨(D - N - 1) / 2, by omega⟩
  have bpar : b = 2 * (α * z1 + β * z2) + (z1 + z2) := by
    rw [hb, hα, hβ]
    ring
  generalize α * z1 + β * z2 = X at bpar
  have hbodd : b % 2 = 1 := by omega
  -- the lower key: `n X_l = Y_l > 0`, with `Y_l = 2 N T + 2dn + 2d + 2n + 2nd` (ring identity)
  have hYl : (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) + (d + n) * (2 - (d - n)) + 2 * n * d =
      2 * N * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * d * n + 2 * d + 2 * n + 2 * n * d := by
    ring
  have hYlpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) + (d + n) * (2 - (d - n)) + 2 * n * d := by
    rw [hYl]
    have h1 := mul_nonneg (show (0 : ℤ) ≤ 2 * N by omega) hTc.le
    have h2 : 0 < d * n := mul_pos (by omega) (by omega)
    have h3 : 0 < d := by omega
    have h4 : 0 < n := by omega
    nlinarith
  obtain ⟨Xl, hXl⟩ : ∃ Xl : ℤ, Xl = (D * (d + n) + N * (d - n)) * (2 - (d - n)) + 2 * d -
      (N - D) * (d ^ 2 + 2 * d * n - n ^ 2) := ⟨_, rfl⟩
  have hkl : n * Xl = (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) + (d + n) * (2 - (d - n)) + 2 * n * d := by
    rw [hXl]
    exact key_lower_neg N D n d hε
  have hXpos : 0 < Xl := by
    have hnX : 0 < n * Xl := by
      rw [hkl]
      exact hYlpos
    exact pos_of_mul_pos_right hnX (by omega)
  have hlo1 := mul_le_mul_of_nonneg_left hs0 hC.le
  have hlowT : (d ^ 2 + 2 * d * n - n ^ 2) * b ≥ Xl + (N - D) * (d ^ 2 + 2 * d * n - n ^ 2) := by
    have e : (d ^ 2 + 2 * d * n - n ^ 2) * b = (D * (d + n) + N * (d - n)) * ((d + n) * z1 + (d - n) * z2)
        - 2 * (n * z1 - d * z2) := hid
    rw [hXl]
    linarith
  have hbl : N - D < b := by
    by_contra hc
    rw [not_lt] at hc
    have := mul_le_mul_of_nonneg_left hc hTc.le
    linarith
  have hlowb : N - D + 2 ≤ b := by omega
  -- the upper key: `n Z_u = Y_u > 0`, with `Y_u = 2 N T + 2 L + 4nd` (ring identity)
  have hYu : (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) - (d + n) * ((d + n) - 2) + 2 * n * (d + n) + 2 * n * d =
      2 * N * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * (d + n) + 4 * n * d := by
    ring
  have hYupos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) - (d + n) * ((d + n) - 2) + 2 * n * (d + n) + 2 * n * d := by
    rw [hYu]
    have h1 := mul_nonneg (show (0 : ℤ) ≤ 2 * N by omega) hTc.le
    have h2 : 0 < n * d := mul_pos (by omega) (by omega)
    nlinarith
  obtain ⟨Zu, hZu⟩ : ∃ Zu : ℤ, Zu = (N + D) * (d ^ 2 + 2 * d * n - n ^ 2) -
      (D * (d + n) + N * (d - n)) * ((d + n) - 2) + 2 * (d + n) + 2 * d := ⟨_, rfl⟩
  have hku : n * Zu = (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N + 1) - (d + n) * ((d + n) - 2) + 2 * n * (d + n) + 2 * n * d := by
    rw [hZu]
    exact key_upper_neg N D n d hε
  have hZpos : 0 < Zu := by
    have hnZ : 0 < n * Zu := by
      rw [hku]
      exact hYupos
    exact pos_of_mul_pos_right hnZ (by omega)
  have hup1 := mul_le_mul_of_nonneg_left hs1 hC.le
  have hupT : (d ^ 2 + 2 * d * n - n ^ 2) * b < (d ^ 2 + 2 * d * n - n ^ 2) * (N + D + 2) := by
    have e : (d ^ 2 + 2 * d * n - n ^ 2) * b = (D * (d + n) + N * (d - n)) * ((d + n) * z1 + (d - n) * z2)
        - 2 * (n * z1 - d * z2) := hid
    rw [hZu] at hZpos
    linarith
  have hbup : b < N + D + 2 := lt_of_mul_lt_mul_left hupT hTc.le
  exact ⟨hlowb, by omega, hbodd⟩

/-- **The residue at the upper odd value (`ε = −1`).** If `b = N + D` then `a ≡ N (mod T_q)` with the window `a − N + k T_q = 0`. -/
theorem core_resid_neg {N D n P Q s m a b : ℤ} (hN : 0 < N) (hND : N < D) (hPQ : N * Q - P * D = -1)
    (hn : n = 2 * N + P) (hPQpar : (P + Q) % 2 = 0) (hs2 : s % 2 = 0) (hb : b = N + D)
    (hnb : n * b = N * s + m) (hab : (N + D) * b - 2 * N * a = (D ^ 2 + 2 * D * N - N ^ 2) * m) :
    ∃ k : ℤ, 0 ≤ a - N + k * (D ^ 2 + 2 * D * N - N ^ 2) ∧
      a - N + k * (D ^ 2 + 2 * D * N - N ^ 2) ≤ D - N := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, s = 2 * σ := ⟨s / 2, by omega⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℤ, P + Q = 2 * τ := ⟨(P + Q) / 2, by omega⟩
  obtain ⟨Tq, hTq⟩ : ∃ T : ℤ, T = D ^ 2 + 2 * D * N - N ^ 2 := ⟨_, rfl⟩
  rw [← hTq] at hab ⊢
  subst hn hb hσ
  have hm1 : m - 1 = 2 * N * (N + D + τ - σ) := by
    linear_combination (-1 : ℤ) * hnb - hPQ + N * hτ
  have hres : 2 * N * (a - N) = -Tq * (m - 1) := by
    linear_combination (-1 : ℤ) * hab - hTq
  have h2 : 2 * N * (a - N + Tq * (N + D + τ - σ)) = 0 := by
    linear_combination hres - Tq * hm1
  have hk : a - N + Tq * (N + D + τ - σ) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · omega
    · exact h
  refine ⟨N + D + τ - σ, ?_, ?_⟩
  · linarith
  · linarith

/-- The even bound at a free V point other than `vLast` (`ε = −1`). -/
theorem neg_even_bounds (frame : ChildFrame) (hε : frame.eps = -1) (hN : 0 < frame.parents.odd.num)
    {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z) (hvL : z ≠ frame.vLast) :
    0 ≤ frame.parentSGrade z ∧ frame.parentSGrade z ≤ 2 * frame.parents.odd.num := by
  by_cases hv : z = vFirst
  · subst hv
    rw [frame.parentSGrade_vFirst]
    constructor <;> omega
  have hdet : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
    have h := frame.odd_det_child
    rw [hε] at h
    exact h
  obtain ⟨hdL, hnL, hD0, hN0, hND, -, -, -, hparL⟩ := frame.linear_facts
  have hop : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨hn0, hnd, -, -, hT⟩ := frame.child_facts
  have hs := FreeVWindow.freeV_even_window frame hz he
  have ht := ArcRanges.arc_even_range frame hz he hv hvL
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  unfold ChildFrame.sGrade at hs0 hs1
  unfold ChildFrame.tGrade at ht0 ht1
  rw [hT] at ht0
  have hpar : (z.1 + z.2) % 2 = 0 := by
    unfold EvenSite at he
    exact he
  exact core_even_neg (N := frame.parents.odd.num) (D := frame.parents.odd.den) (n := frame.child.num)
    (d := frame.child.den) (z1 := z.1) (z2 := z.2) (b := frame.parentSGrade z) hN hND (by omega)
    (by omega) hdet (by omega) hpar rfl hs0 hs1 (by linarith) (by linarith)

/-- The odd bounds at a free V point (`ε = −1`). -/
theorem neg_odd_bounds (frame : ChildFrame) (hε : frame.eps = -1) (hN : 0 < frame.parents.odd.num)
    {z : Site} (hz : z ∈ frame.freeV) (he : ¬ EvenSite z) :
    frame.parents.odd.num - frame.parents.odd.den + 2 ≤ frame.parentSGrade z ∧
      frame.parentSGrade z ≤ frame.parents.odd.num + frame.parents.odd.den ∧
      frame.parentSGrade z % 2 = 1 := by
  have hdet : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
    have h := frame.odd_det_child
    rw [hε] at h
    exact h
  obtain ⟨hdL, hnL, hD0, hN0, hND, -, -, -, -⟩ := frame.linear_facts
  have hop : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨hn0, hnd, -, -, hT⟩ := frame.child_facts
  have hs := FreeVWindow.freeV_odd_window frame hz he
  have ht := ArcRanges.arc_odd_range frame hz he
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  unfold ChildFrame.sGrade at hs0 hs1
  unfold ChildFrame.tGrade at ht0 ht1
  rw [hT] at ht0
  have hodd : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at he
    omega
  exact core_odd_neg (N := frame.parents.odd.num) (D := frame.parents.odd.den) (n := frame.child.num)
    (d := frame.child.den) (z1 := z.1) (z2 := z.2) (b := frame.parentSGrade z) hN hND (by omega)
    (by omega) hdet (by omega) hodd rfl hs0 hs1 (by linarith) (by linarith)

/-- The residue at an odd point with `b = N + D` (`ε = −1`). -/
theorem neg_residue (frame : ChildFrame) (hε : frame.eps = -1) (hN : 0 < frame.parents.odd.num)
    {z : Site} (hb : frame.parentSGrade z = frame.parents.odd.num + frame.parents.odd.den) :
    ∃ k : ℤ, 0 ≤ frame.parentTGrade z - frame.parents.odd.num +
        k * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) ∧
      frame.parentTGrade z - frame.parents.odd.num +
        k * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) ≤
          frame.parents.odd.den - frame.parents.odd.num := by
  have hdet : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
    have h := frame.odd_det_child
    rw [hε] at h
    exact h
  have hdetE : frame.parents.odd.num * frame.parents.even.den -
      frame.parents.even.num * frame.parents.odd.den = -1 := by
    have h := frame.eps_det_even
    rw [hε] at h
    exact h
  obtain ⟨hdL, hnL, hD0, hN0, hND, -, -, -, -⟩ := frame.linear_facts
  have hep : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hs2 : frame.sGrade z % 2 = 0 := frame.sGrade_mod_two z
  have hnb : frame.child.num * frame.parentSGrade z =
      frame.parents.odd.num * frame.sGrade z + (z.1 + z.2) :=
    id_nb_neg _ _ _ _ _ _ hdet
  have hab : (frame.parents.odd.num + frame.parents.odd.den) * frame.parentSGrade z -
      2 * frame.parents.odd.num * frame.parentTGrade z =
      (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
        frame.parents.odd.num ^ 2) * (z.1 + z.2) :=
    id_ab_neg _ _ _ _
  have hnL' : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := hnL
  exact core_resid_neg (N := frame.parents.odd.num) (D := frame.parents.odd.den) (n := frame.child.num)
    (P := frame.parents.even.num) (Q := frame.parents.even.den) (s := frame.sGrade z)
    (m := z.1 + z.2) (b := frame.parentSGrade z) (a := frame.parentTGrade z) hN hND hdetE hnL' hep hs2 hb
    hnb hab

end FLatticePaper.LeftVNegProof
