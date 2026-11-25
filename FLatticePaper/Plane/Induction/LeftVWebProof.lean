import FLatticePaper.Plane.Induction.LeftVGrade
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.ArcRanges

/-! # The left V-web input, proved (`ε = +1`)

`LeftVWeb` (the named input of `LeftVGrade`) is derived from the free-V windows (`FreeVWindow`, `ArcRanges`) and the integer
identities of the child `(n, d)` over the odd parent `(N, D)` (`N d − D n = 1`), with `T` the child period, `T_q` the parent's:

* `T b = C s + 2 t`, `n b = N s − m`, `n C = N T − L`, `(N + D) b − 2 N a = T_q m` (`a = t_p`, `b = s_p`, `m = z₁ + z₂`);
* even `z`: `s ∈ [0, 2n]`, `t ∈ [2L − T, −L]`, so `−1 ≤ b < 2N`; `b` is even, so `0 ≤ b ≤ 2N`;
* odd `z`: `s ∈ [2 − (d − n), L − 2]`, `t ∈ [L + d − T, −d]`, so `N − D ≤ b ≤ N + D − 2`, with `b` odd;
* odd `z`, `b ≤ N − D + 1`: `b = N − D`, and then `2N (a − D) = −T_q (m + 1)` with `m + 1 = 2N k`, so `a − N + k T_q = D − N`. -/

namespace FLatticePaper.LeftVWebProof

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.LeftVGrade

/-- `T b = C s + 2 t` (`ε = +1`). -/
theorem id_Tb (N D n d z1 z2 : ℤ) (hε : N * d - D * n = 1) :
    (d ^ 2 + 2 * d * n - n ^ 2) * ((D + N) * z1 + (D - N) * z2) =
      (D * (d + n) + N * (d - n)) * ((d + n) * z1 + (d - n) * z2) + 2 * (n * z1 - d * z2) := by
  linear_combination (2 * (n * z1 - d * z2)) * hε

/-- `n b = N s − m` (`ε = +1`). -/
theorem id_nb (N D n d z1 z2 : ℤ) (hε : N * d - D * n = 1) :
    n * ((D + N) * z1 + (D - N) * z2) = N * ((d + n) * z1 + (d - n) * z2) - (z1 + z2) := by
  linear_combination (-(z1 + z2)) * hε

/-- `n C = N T − L` (`ε = +1`). -/
theorem id_nC (N D n d : ℤ) (hε : N * d - D * n = 1) :
    n * (D * (d + n) + N * (d - n)) = N * (d ^ 2 + 2 * d * n - n ^ 2) - (d + n) := by
  linear_combination (-d - n) * hε

/-- The lower-bound identity: `n · X = T (2N − 1) + L (L − 2) + 2nd`, with `X = C (2 − c) + 2L + 2d − (N − D) T` (`ε = +1`). -/
theorem key_lower (N D n d : ℤ) (hε : N * d - D * n = 1) :
    n * ((D * (d + n) + N * (d - n)) * (2 - (d - n)) + 2 * (d + n) + 2 * d -
        (N - D) * (d ^ 2 + 2 * d * n - n ^ 2)) =
      (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N - 1) + (d + n) * ((d + n) - 2) + 2 * n * d := by
  linear_combination (-2 * (d * n + d + n)) * hε

/-- The upper-bound identity: `n · Z = T (2N − 1) + L (L − 2) + 2nd`, with `Z = (N + D) T − C (L − 2) + 2d` (`ε = +1`). -/
theorem key_upper (N D n d : ℤ) (hε : N * d - D * n = 1) :
    n * ((N + D) * (d ^ 2 + 2 * d * n - n ^ 2) - (D * (d + n) + N * (d - n)) * ((d + n) - 2) + 2 * d) =
      (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N - 1) + (d + n) * ((d + n) - 2) + 2 * n * d := by
  linear_combination (-2 * (d - n ^ 2 + n)) * hε

/-- The parent identity `(N + D) b − 2 N a = T_q (z₁ + z₂)` (no relation needed). -/
theorem id_ab (N D z1 z2 : ℤ) :
    (N + D) * ((D + N) * z1 + (D - N) * z2) - 2 * N * (N * z1 - D * z2) =
      (D ^ 2 + 2 * D * N - N ^ 2) * (z1 + z2) := by
  ring

/-- **The even bound.** For an even point with `s ∈ [0, 2n]` and `t ∈ [2L − T, −L]`: `0 ≤ b ≤ 2N`. -/
theorem core_even {N D n d z1 z2 b : ℤ} (hN : 0 < N) (hND : N < D) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hε : N * d - D * n = 1) (hDN : (D + N) % 2 = 1) (hpar : (z1 + z2) % 2 = 0)
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
  have hid := id_Tb N D n d z1 z2 hε
  rw [← hb] at hid
  have hnC := id_nC N D n d hε
  have hup1 := mul_le_mul_of_nonneg_left hs1 hC.le
  have hlo1 := mul_le_mul_of_nonneg_left hs0 hC.le
  -- upper: `T b ≤ 2 N T − 4 L < 2 N T`
  have hlt : (d ^ 2 + 2 * d * n - n ^ 2) * b < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N) := by
    linarith
  have hbup : b < 2 * N := lt_of_mul_lt_mul_left hlt hTc.le
  -- lower: `T (b + 2) ≥ 4 L > 0`, so `b ≥ −1`
  have hpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (b + 2) := by
    have : (d ^ 2 + 2 * d * n - n ^ 2) * (b + 2) = (d ^ 2 + 2 * d * n - n ^ 2) * b + 2 * (d ^ 2 + 2 * d * n - n ^ 2) := by
      ring
    linarith
  have hb2 : 0 < b + 2 := pos_of_mul_pos_right hpos hTc.le
  -- parity: `b ≡ z1 + z2 (mod 2)`, and `z1 + z2` is even
  obtain ⟨α, hα⟩ : ∃ α : ℤ, D + N = 2 * α + 1 := ⟨(D + N - 1) / 2, by omega⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, D - N = 2 * β + 1 := ⟨(D - N - 1) / 2, by omega⟩
  have bpar : b = 2 * (α * z1 + β * z2) + (z1 + z2) := by
    rw [hb, hα, hβ]
    ring
  generalize α * z1 + β * z2 = X at bpar
  constructor <;> omega

/-- **The odd bounds.** For an odd point with `s ∈ [2 − (d − n), L − 2]` and `t ∈ [L + d − T, −d]`:
`N − D ≤ b ≤ N + D − 2`, and `b` is odd. -/
theorem core_odd {N D n d z1 z2 b : ℤ} (hN : 0 < N) (hND : N < D) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hε : N * d - D * n = 1) (hDN : (D + N) % 2 = 1) (hodd : (z1 + z2) % 2 = 1)
    (hb : b = (D + N) * z1 + (D - N) * z2)
    (hs0 : 2 - (d - n) ≤ (d + n) * z1 + (d - n) * z2) (hs1 : (d + n) * z1 + (d - n) * z2 ≤ (d + n) - 2)
    (ht0 : (d + n) + d - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * z1 - d * z2)
    (ht1 : n * z1 - d * z2 ≤ -d) :
    N - D ≤ b ∧ b ≤ N + D - 2 ∧ b % 2 = 1 := by
  have hdn : n < d := by omega
  have hTc : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by
    have h1 : n * n < d * d := mul_self_lt_mul_self (by omega) hdn
    have h2 : 0 < d * n := mul_pos (by omega) (by omega)
    nlinarith [h1, h2]
  have hC : 0 < D * (d + n) + N * (d - n) := by
    have h1 := mul_pos (show (0 : ℤ) < D by omega) (show (0 : ℤ) < d + n by omega)
    have h2 := mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ d - n by omega)
    linarith
  have hid := id_Tb N D n d z1 z2 hε
  rw [← hb] at hid
  obtain ⟨α, hα⟩ : ∃ α : ℤ, D + N = 2 * α + 1 := ⟨(D + N - 1) / 2, by omega⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, D - N = 2 * β + 1 := ⟨(D - N - 1) / 2, by omega⟩
  have bpar : b = 2 * (α * z1 + β * z2) + (z1 + z2) := by
    rw [hb, hα, hβ]
    ring
  generalize α * z1 + β * z2 = X at bpar
  have hbodd : b % 2 = 1 := by omega
  -- positivity of the common right-hand side
  have hYpos : 0 < (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N - 1) + (d + n) * ((d + n) - 2) + 2 * n * d := by
    have h1 := mul_pos hTc (show (0 : ℤ) < 2 * N - 1 by omega)
    have h2 := mul_nonneg (show (0 : ℤ) ≤ d + n by omega) (show (0 : ℤ) ≤ (d + n) - 2 by omega)
    have h3 := mul_nonneg (show (0 : ℤ) ≤ 2 * n by omega) (show (0 : ℤ) ≤ d by omega)
    linarith
  -- lower: `X_l > 0`, hence `b > N − D − 2`, and with parity `b ≥ N − D`
  obtain ⟨Xl, hXl⟩ : ∃ Xl : ℤ, Xl = (D * (d + n) + N * (d - n)) * (2 - (d - n)) + 2 * (d + n) + 2 * d -
      (N - D) * (d ^ 2 + 2 * d * n - n ^ 2) := ⟨_, rfl⟩
  have hkl : n * Xl = (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N - 1) + (d + n) * ((d + n) - 2) + 2 * n * d := by
    rw [hXl]
    exact key_lower N D n d hε
  have hXpos : 0 < Xl := by
    have hnX : 0 < n * Xl := by
      rw [hkl]
      exact hYpos
    exact pos_of_mul_pos_right hnX (by omega)
  have hlo1 := mul_le_mul_of_nonneg_left hs0 hC.le
  have hlowT : (d ^ 2 + 2 * d * n - n ^ 2) * b ≥ Xl + (N - D - 2) * (d ^ 2 + 2 * d * n - n ^ 2) := by
    have e : (d ^ 2 + 2 * d * n - n ^ 2) * b = (D * (d + n) + N * (d - n)) * ((d + n) * z1 + (d - n) * z2)
        + 2 * (n * z1 - d * z2) := hid
    rw [hXl] at hXpos ⊢
    linarith
  have hbl : N - D - 2 < b := by
    by_contra hc
    rw [not_lt] at hc
    have := mul_le_mul_of_nonneg_left hc hTc.le
    linarith
  have hlowb : N - D ≤ b := by omega
  -- upper: `Z_u > 0`, hence `b < N + D`, and with parity `b ≤ N + D − 2`
  obtain ⟨Zu, hZu⟩ : ∃ Zu : ℤ, Zu = (N + D) * (d ^ 2 + 2 * d * n - n ^ 2) -
      (D * (d + n) + N * (d - n)) * ((d + n) - 2) + 2 * d := ⟨_, rfl⟩
  have hku : n * Zu = (d ^ 2 + 2 * d * n - n ^ 2) * (2 * N - 1) + (d + n) * ((d + n) - 2) + 2 * n * d := by
    rw [hZu]
    exact key_upper N D n d hε
  have hZpos : 0 < Zu := by
    have hnZ : 0 < n * Zu := by
      rw [hku]
      exact hYpos
    exact pos_of_mul_pos_right hnZ (by omega)
  have hup1 := mul_le_mul_of_nonneg_left hs1 hC.le
  have hupT : (d ^ 2 + 2 * d * n - n ^ 2) * b < (N + D) * (d ^ 2 + 2 * d * n - n ^ 2) := by
    have e : (d ^ 2 + 2 * d * n - n ^ 2) * b = (D * (d + n) + N * (d - n)) * ((d + n) * z1 + (d - n) * z2)
        + 2 * (n * z1 - d * z2) := hid
    rw [hZu] at hZpos
    linarith
  have hbup : b < N + D := by
    have := lt_of_mul_lt_mul_left (by linarith [hupT] : (d ^ 2 + 2 * d * n - n ^ 2) * b <
      (d ^ 2 + 2 * d * n - n ^ 2) * (N + D)) hTc.le
    linarith
  exact ⟨hlowb, by omega, hbodd⟩

/-- **The residue core.** For an odd point with `b = N − D` (the only odd value in the V-range), `a ≡ D (mod T_q)`:
`a − N + k T_q = D − N` for `k = σ + (D − N) + κ`, where `s = 2σ` and `Q − P = 2κ`. -/
theorem core_resid {N D n P Q s b a m : ℤ} (hN : 0 < N) (hND : N < D) (hPQ : N * Q - P * D = 1)
    (hn : n = 2 * N + P) (hPQpar : (P + Q) % 2 = 0) (hs2 : s % 2 = 0) (hb : b = N - D)
    (hnb : n * b = N * s - m) (hab : (N + D) * b - 2 * N * a = (D ^ 2 + 2 * D * N - N ^ 2) * m) :
    ∃ k : ℤ, 0 ≤ a - N + k * (D ^ 2 + 2 * D * N - N ^ 2) ∧
      a - N + k * (D ^ 2 + 2 * D * N - N ^ 2) ≤ D - N := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, s = 2 * σ := ⟨s / 2, by omega⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, Q - P = 2 * κ := ⟨(Q - P) / 2, by omega⟩
  obtain ⟨Tq, hTq⟩ : ∃ T : ℤ, T = D ^ 2 + 2 * D * N - N ^ 2 := ⟨_, rfl⟩
  rw [← hTq] at hab ⊢
  subst hn hb hσ
  have hm1 : m + 1 = 2 * N * (σ + (D - N) + κ) := by
    linear_combination hnb - hPQ + N * hκ
  have hres : 2 * N * (a - D) = -Tq * (m + 1) := by
    linear_combination (-1 : ℤ) * hab + hTq
  have h2 : 2 * N * (a - D + Tq * (σ + (D - N) + κ)) = 0 := by
    linear_combination hres - Tq * hm1
  have hk : a - D + Tq * (σ + (D - N) + κ) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · omega
    · exact h
  refine ⟨σ + (D - N) + κ, ?_, ?_⟩
  · linarith
  · linarith

/-- The odd-`z` bounds of `freeV`, assembled from the windows and the arc `t`-range. -/
theorem freeV_odd_bounds (frame : ChildFrame) (hε : frame.eps = 1) (hN : 0 < frame.parents.odd.num)
    {z : Site} (hz : z ∈ frame.freeV) (he : ¬ EvenSite z) :
    frame.parents.odd.num - frame.parents.odd.den ≤ frame.parentSGrade z ∧
      frame.parentSGrade z ≤ frame.parents.odd.num + frame.parents.odd.den - 2 ∧
      frame.parentSGrade z % 2 = 1 := by
  have hdet : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = 1 := by
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
  exact core_odd (N := frame.parents.odd.num) (D := frame.parents.odd.den) (n := frame.child.num)
    (d := frame.child.den) (z1 := z.1) (z2 := z.2) (b := frame.parentSGrade z) hN hND (by omega)
    (by omega) hdet (by omega) hodd rfl hs0 hs1 (by linarith) (by linarith)

/-- **The left V-web input, proved.** For `ε = +1` with `N > 0`, the three clauses of `LeftVWeb`. -/
theorem leftVWeb_of_eps_one (frame : ChildFrame) (hε : frame.eps = 1) (hN : 0 < frame.parents.odd.num) :
    LeftVWeb frame := by
  have hdet : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = 1 := by
    have h := frame.odd_det_child
    rw [hε] at h
    exact h
  have hdetE : frame.parents.odd.num * frame.parents.even.den -
      frame.parents.even.num * frame.parents.odd.den = 1 := by
    have h := frame.eps_det_even
    rw [hε] at h
    exact h
  obtain ⟨hdL, hnL, hD0, hN0, hND, -, -, -, hparL⟩ := frame.linear_facts
  have hep : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hop : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨hn0, hnd, -, -, hT⟩ := frame.child_facts
  unfold LeftVWeb
  refine ⟨?_, ?_, ?_⟩
  · intro z hz he
    by_cases hv : z = vFirst
    · subst hv
      rw [frame.parentSGrade_vFirst]
      constructor <;> omega
    by_cases hvL : z = frame.vLast
    · subst hvL
      rw [frame.parentSGrade_vLast, hε]
      constructor <;> omega
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
    exact core_even (N := frame.parents.odd.num) (D := frame.parents.odd.den) (n := frame.child.num)
      (d := frame.child.den) (z1 := z.1) (z2 := z.2) (b := frame.parentSGrade z) hN hND (by omega)
      (by omega) hdet (by omega) hpar rfl hs0 hs1 (by linarith) (by linarith)
  · intro z hz he
    have hb := freeV_odd_bounds frame hε hN hz he
    exact ⟨by linarith [hb.2.1], by linarith [hb.1]⟩
  · intro z hz he hbl
    have hb := freeV_odd_bounds frame hε hN hz he
    have hbND : frame.parentSGrade z = frame.parents.odd.num - frame.parents.odd.den := by
      omega
    have hs2 : frame.sGrade z % 2 = 0 := frame.sGrade_mod_two z
    have hnb : frame.child.num * frame.parentSGrade z =
        frame.parents.odd.num * frame.sGrade z - (z.1 + z.2) :=
      id_nb _ _ _ _ _ _ hdet
    have hab : (frame.parents.odd.num + frame.parents.odd.den) * frame.parentSGrade z -
        2 * frame.parents.odd.num * frame.parentTGrade z =
        (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num -
          frame.parents.odd.num ^ 2) * (z.1 + z.2) :=
      id_ab _ _ _ _
    have hnL' : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := hnL
    exact core_resid (N := frame.parents.odd.num) (D := frame.parents.odd.den) (n := frame.child.num)
      (P := frame.parents.even.num) (Q := frame.parents.even.den) (s := frame.sGrade z)
      (m := z.1 + z.2) (b := frame.parentSGrade z) (a := frame.parentTGrade z) hN
      (by linarith [hb.2.2]) hdetE hnL' hep hs2 hbND hnb hab

/-- **The left-arc conjugate freeness, with the V-web proved** (`ε = +1`). -/
theorem left_V_not_nonfree_proved (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hε : (frameAt word).eps = 1) {z : Site} (hz : z ∈ (frameAt word).freeV) :
    ¬ Nonfree (frameAt (conjWord word)) (zTurn (z - (frameAt word).sheetShift)) := by
  have hN : 0 < (frameAt word).parents.odd.num := by
    obtain ⟨hGn, hGd⟩ := conj_child_num_den (frame := frameAt word) (conj := frameAt (conjWord word))
      (frameAt_conj_child hw)
    obtain ⟨-, hGlt, -, -, -⟩ := (frameAt (conjWord word)).child_facts
    rw [hGn, hGd] at hGlt
    omega
  exact LeftVGrade.left_V_not_nonfree word hw hε (leftVWeb_of_eps_one (frameAt word) hε hN) hz

end FLatticePaper.LeftVWebProof
