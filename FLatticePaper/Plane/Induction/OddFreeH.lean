import FLatticePaper.Plane.Induction.VPathFloor
import FLatticePaper.Plane.Induction.SheetCases

/-! Task 72 (V-block converse, odd conjugate free H points and `V_p + I`).

An odd free H point `w` of the conjugate child `(D − N, D + N)` is `w = (2l + 1 − b, b)`, and its transport
`zTurn w = (−b, 2l − b)` is governed by `r = (D − N) l − D b`:

* the H spectrum `t_c(w) = 2r + (D − N)` gives `0 ≤ r ≤ N`, and the polygon bound on `s_c` gives `0 ≤ l ≤ D − 1`
  (`odd_block_arith`);
* `r = N` forces `l = D − 1` and `b = D − 1 − N`, so `zTurn w = excVertex = V_p + I` (`odd_freeH_image`, right case);
* `r ≤ N − 1` gives `q = (d − n) l − d b ≤ n`, so `zTurn w` is a block vertex of the word frame's free V cut
  (`even_block_mem_freeV`, and the origin `l = 0` by `origin_mem_freeV`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The origin is a free V point of any child frame. -/
theorem origin_mem_freeV (frame : ChildFrame) : ((0 : ℤ), (0 : ℤ)) ∈ frame.freeV := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hdpos : 0 < frame.child.den := by omega
  have hnn : 0 ≤ frame.child.num := by omega
  have hnl : frame.child.num < frame.child.den := by omega
  have hd3 : 3 ≤ frame.child.den := by omega
  have hT0 := frame.periodDen_nonneg
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    unfold Fraction.periodDenominator
    nlinarith
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.mem_closedPolygon_iff]
    left
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold EvenSite
      dsimp only
      omega
    · unfold ChildFrame.tGrade
      dsimp only
      linarith
    · unfold ChildFrame.tGrade
      dsimp only
      linarith
    · unfold ChildFrame.sGrade
      dsimp only
      linarith
    · unfold ChildFrame.sGrade
      dsimp only
      nlinarith
  · show ((0 : ℤ) - 1, (0 : ℤ)) ∉ frame.closedPolygon
    intro hmem
    rw [frame.mem_closedPolygon_iff] at hmem
    rcases hmem with ⟨hE, -, -, -, -⟩ | ⟨-, -, -, hs0, -⟩
    · unfold EvenSite at hE
      dsimp only at hE
      omega
    · unfold ChildFrame.sGrade at hs0
      dsimp only at hs0
      nlinarith
  · unfold ChildFrame.vSpectrum
    unfold ChildFrame.sGrade
    dsimp only
    exact ⟨by norm_num, Or.inl ⟨by norm_num, by nlinarith⟩⟩

/-- **The even block vertex.** For `1 ≤ l < D`, with `b = ⌊(d − n) l / d⌋` and `q = (d − n) l − d b ≤ n`, the vertex
`(−b, 2l − b)` lies in the word frame's free V cut. Its `s` is `2q`, and its left neighbour has `s = 2q − (d + n) < 2 − d + n`. -/
theorem even_block_mem_freeV (frame : ChildFrame) (l : ℤ) (hl1 : 1 ≤ l) (hl2 : l < frame.parents.odd.den)
    (hq : (frame.child.den - frame.child.num) * l -
      frame.child.den * ((frame.child.den - frame.child.num) * l / frame.child.den) ≤ frame.child.num) :
    (-((frame.child.den - frame.child.num) * l / frame.child.den),
      2 * l - (frame.child.den - frame.child.num) * l / frame.child.den) ∈ frame.freeV := by
  obtain ⟨hd, hn, hD, hN0, hND, hq0, hn0, hnq, hpar⟩ := frame.linear_facts
  have hdpos : 0 < frame.child.den := by omega
  have hnl : frame.child.num < frame.child.den := by omega
  have hnn : 0 ≤ frame.child.num := by omega
  have hdn : 0 ≤ frame.child.den - frame.child.num := by omega
  have hl0 : 0 ≤ l := by omega
  have hd3 : 3 ≤ frame.child.den := by omega
  have hl2' : 2 * l ≤ frame.child.den - 3 := by omega
  have hT0 := frame.periodDen_nonneg
  obtain ⟨b, hb⟩ : ∃ b, (frame.child.den - frame.child.num) * l / frame.child.den = b := ⟨_, rfl⟩
  rw [hb] at hq ⊢
  have hb0 : 0 ≤ b := by
    rw [← hb]
    exact Int.ediv_nonneg (mul_nonneg hdn hl0) hdpos.le
  have hbl : b ≤ l := by
    have hA := Int.ediv_mul_le ((frame.child.den - frame.child.num) * l) hdpos.ne'
    rw [hb] at hA
    by_contra hc
    have h5 : l + 1 ≤ b := by omega
    nlinarith [mul_le_mul_of_nonneg_right h5 hdpos.le, mul_nonneg hnn hl0]
  have hq' := frame.block_q_bounds l hl1 (by omega)
  rw [hb] at hq'
  obtain ⟨q, hqdef⟩ : ∃ q, q = (frame.child.den - frame.child.num) * l - frame.child.den * b := ⟨_, rfl⟩
  rw [← hqdef] at hq' hq
  obtain ⟨hq1, -⟩ := hq'
  have hs : frame.sGrade (-b, 2 * l - b) = 2 * q := by
    rw [hqdef]
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have hsn : frame.sGrade (-b - 1, 2 * l - b) = 2 * q - (frame.child.den + frame.child.num) := by
    rw [hqdef]
    unfold ChildFrame.sGrade
    dsimp only
    ring
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.mem_closedPolygon_iff]
    left
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold EvenSite
      dsimp only
      omega
    · unfold ChildFrame.tGrade Fraction.periodDenominator
      dsimp only
      nlinarith [mul_le_mul_of_nonneg_left hbl hnn, mul_le_mul_of_nonneg_left hl2' (show (0 : ℤ) ≤ frame.child.num + 2 * frame.child.den by omega),
        mul_nonneg hdpos.le hb0, mul_nonneg hnn hdn, sq_nonneg frame.child.num]
    · unfold ChildFrame.tGrade
      dsimp only
      nlinarith [mul_le_mul_of_nonneg_left hbl hdpos.le, mul_nonneg hn0 hb0, mul_le_mul_of_nonneg_left hl1 hdpos.le]
    · rw [hs]
      omega
    · rw [hs]
      omega
  · show (-b - 1, 2 * l - b) ∉ frame.closedPolygon
    intro hmem
    rw [frame.mem_closedPolygon_iff] at hmem
    rcases hmem with ⟨hE, -, -, -, -⟩ | ⟨-, -, -, hs0, -⟩
    · unfold EvenSite at hE
      dsimp only at hE
      omega
    · rw [hsn] at hs0
      omega
  · unfold ChildFrame.vSpectrum
    rw [hs]
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩

/-- **The odd arithmetic.** With `σ = 2Dl − (D − N) b` and `r = (D − N) l − D b ∈ [0, N]`, the identity `D σ = T_p l + (D − N) r`
and the polygon band `1 − N ≤ σ + D ≤ T_p + D − 1` force `0 ≤ l ≤ D − 1`. -/
theorem odd_block_arith (D N l b : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D)
    (hr0 : 0 ≤ (D - N) * l - D * b) (hr1 : (D - N) * l - D * b ≤ N)
    (hs0 : 1 - N ≤ 2 * D * l - (D - N) * b + D)
    (hs1 : 2 * D * l - (D - N) * b + D ≤ (D ^ 2 + 2 * D * N - N ^ 2) + D - 1) :
    0 ≤ l ∧ l ≤ D - 1 := by
  have hD : 0 < D := by omega
  have hDN : 0 ≤ D - N := by omega
  have hTp0 : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have key : D * (2 * D * l - (D - N) * b) =
      (D ^ 2 + 2 * D * N - N ^ 2) * l + (D - N) * ((D - N) * l - D * b) := by ring
  constructor
  · by_contra hl
    have hl' : l ≤ -1 := by omega
    have h1 : (D ^ 2 + 2 * D * N - N ^ 2) * l ≤ -(D ^ 2 + 2 * D * N - N ^ 2) := by
      nlinarith
    have h2 : (D - N) * ((D - N) * l - D * b) ≤ (D - N) * N := mul_le_mul_of_nonneg_left hr1 hDN
    have h3 : D * (1 - N - D) ≤ D * (2 * D * l - (D - N) * b) :=
      mul_le_mul_of_nonneg_left (by linarith) hD.le
    nlinarith [key, h1, h2, h3]
  · by_contra hl
    have hl' : D ≤ l := by omega
    have h1 : (D ^ 2 + 2 * D * N - N ^ 2) * D ≤ (D ^ 2 + 2 * D * N - N ^ 2) * l :=
      mul_le_mul_of_nonneg_left hl' hTp0
    have h2 : D * (2 * D * l - (D - N) * b) ≤ D * ((D ^ 2 + 2 * D * N - N ^ 2) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hD.le
    have h3 : 0 ≤ (D - N) * ((D - N) * l - D * b) := mul_nonneg hDN hr0
    nlinarith [key, h1, h2, h3]

/-- **The odd conjugate free H point, transported.** For an odd free H point `w` of the conjugate child, `zTurn w` is either a
free V point of the word frame, or the exceptional vertex `V_p + I`. -/
theorem odd_freeH_image {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt (conjWord word)).freeH) (hwO : ¬ EvenSite w) :
    zTurn w ∈ (frameAt word).freeV ∨ zTurn w = excVertex (frameAt word) := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn0', hd0'⟩ := conj_child_num_den hc
  have hT0' := conj_periodDenominator h
  unfold oddParentPeriod at hT0'
  have hN1 := frameAt_odd_num_pos h
  obtain ⟨hdW, hnW, hDpos, hN0, hNlt, hdq, hn0, hnq, hpar⟩ := (frameAt word).linear_facts
  have hod : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hε := (frameAt word).eps_eq
  have hε1 := (frameAt word).eps_unit
  obtain ⟨D, hDg⟩ : ∃ D, (frameAt word).parents.odd.den = D := ⟨_, rfl⟩
  obtain ⟨N, hNg⟩ : ∃ N, (frameAt word).parents.odd.num = N := ⟨_, rfl⟩
  rw [hDg, hNg] at hn0' hd0' hT0' hod hε hNlt
  rw [hDg] at hDpos hdW
  rw [hNg] at hN1 hN0
  have hεN : N * (frameAt word).child.den - D * (frameAt word).child.num = 1 ∨
      N * (frameAt word).child.den - D * (frameAt word).child.num = -1 := by
    rw [← hε]
    exact hε1
  have hND : N + 1 ≤ D := by omega
  have hN1' : 1 ≤ N := by omega
  have hdpos : 0 < (frameAt word).child.den := by omega
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hw
  obtain ⟨hmem, -, hsp⟩ := hw
  obtain ⟨c, hc'⟩ := (frameAt (conjWord word)).tGrade_parity w
  have htb : D - N ≤ (frameAt (conjWord word)).tGrade w ∧ (frameAt (conjWord word)).tGrade w ≤ D + N := by
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
    · unfold EvenSite at hwO
      omega
    · constructor <;> omega
  have hs01 : 2 - (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num ≤
        (frameAt (conjWord word)).sGrade w ∧
      (frameAt (conjWord word)).sGrade w ≤ (frameAt (conjWord word)).child.periodDenominator +
        (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2 := by
    rcases ((frameAt (conjWord word)).mem_closedPolygon_iff w).1 hmem with
      ⟨hE, -, -, -, -⟩ | ⟨-, -, -, hs0, hs1⟩
    · exact absurd hE hwO
    · exact ⟨hs0, hs1⟩
  obtain ⟨hs0, hs1⟩ := hs01
  obtain ⟨l, hl⟩ : ∃ l : ℤ, w.1 + w.2 = 2 * l + 1 :=
    ⟨(w.1 + w.2 - 1) / 2, by unfold EvenSite at hwO; omega⟩
  have hw1 : w.1 = 2 * l + 1 - w.2 := by omega
  have ht_def : (frameAt (conjWord word)).tGrade w =
      (frameAt (conjWord word)).child.num * w.1 - (frameAt (conjWord word)).child.den * w.2 := rfl
  have hs_def : (frameAt (conjWord word)).sGrade w =
      ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) * w.1 +
        ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) * w.2 := rfl
  have e_s : (frameAt (conjWord word)).sGrade w = 2 * (2 * D * l - (D - N) * w.2 + D) := by
    rw [hs_def, hn0', hd0', hw1]
    ring
  have hσ0 : 1 - N ≤ 2 * D * l - (D - N) * w.2 + D := by
    have := hs0
    rw [e_s, hn0', hd0'] at this
    linarith
  have hσ1 : 2 * D * l - (D - N) * w.2 + D ≤ (D ^ 2 + 2 * D * N - N ^ 2) + D - 1 := by
    have := hs1
    rw [e_s, hT0', hn0', hd0'] at this
    linarith
  have htE : (frameAt (conjWord word)).tGrade w = 2 * ((D - N) * l - D * w.2) + (D - N) := by
    rw [ht_def, hn0', hd0', hw1]
    ring
  have hR0 : 0 ≤ (D - N) * l - D * w.2 := by
    have := htb.1
    rw [htE] at this
    linarith
  have hR1 : (D - N) * l - D * w.2 ≤ N := by
    have := htb.2
    rw [htE] at this
    linarith
  obtain ⟨hl0, hlD⟩ := odd_block_arith D N l w.2 hN1' hND hR0 hR1 hσ0 hσ1
  have hzeq : zTurn w = (-w.2, 2 * l - w.2) := by
    unfold zTurn
    exact Prod.ext rfl (by show w.1 - 1 = 2 * l - w.2; omega)
  by_cases hrN : (D - N) * l - D * w.2 = N
  · -- the case `r = N`: `l = D − 1`, `b = D − 1 − N`, so `zTurn w = V_p + I`
    right
    have hrN' : N * (l + 1) = D * (l - w.2) := by linear_combination (-1 : ℤ) * hrN
    have hkey : (N * (frameAt word).child.den - D * (frameAt word).child.num) * (l + 1) =
        D * ((frameAt word).child.den * (l - w.2) - (frameAt word).child.num * (l + 1)) := by
      linear_combination (frameAt word).child.den * hrN'
    obtain ⟨X, hX⟩ : ∃ X, l + 1 = D * X := by
      rcases hεN with h1 | h1
      · rw [h1] at hkey
        exact ⟨(frameAt word).child.den * (l - w.2) - (frameAt word).child.num * (l + 1), by linarith⟩
      · rw [h1] at hkey
        exact ⟨-((frameAt word).child.den * (l - w.2) - (frameAt word).child.num * (l + 1)), by linarith⟩
    have hX1 : X = 1 := by
      rcases (show X ≤ 0 ∨ X = 1 ∨ 2 ≤ X by omega) with h0 | h1 | h2
      · linarith [mul_le_mul_of_nonneg_left h0 hDpos.le]
      · exact h1
      · linarith [mul_le_mul_of_nonneg_left h2 hDpos.le]
    subst hX1
    have hlD1 : l = D - 1 := by linarith
    have hbD : w.2 = D - 1 - N := by
      have h0 : D * (w.2 - (D - 1 - N)) = 0 := by
        rw [hlD1] at hrN
        linear_combination (-1 : ℤ) * hrN
      rcases mul_eq_zero.1 h0 with h0 | h0
      · omega
      · linarith
    rw [hzeq]
    unfold excVertex
    rw [hDg, hNg]
    exact Prod.ext (by show -w.2 = N - D + 1; omega) (by show 2 * l - w.2 = D + N - 1; omega)
  · left
    have hrle : (D - N) * l - D * w.2 ≤ N - 1 := by omega
    rcases (show l = 0 ∨ 1 ≤ l by omega) with h0 | h1
    · -- the origin: `l = 0` forces `b = 0`
      subst h0
      have hb1 : 0 ≤ w.2 := by
        by_contra hc2
        linarith [mul_le_mul_of_nonneg_left (show w.2 ≤ -1 by omega) hDpos.le]
      have hb2 : w.2 ≤ 0 := by
        by_contra hc2
        linarith [mul_le_mul_of_nonneg_left (show 1 ≤ w.2 by omega) hDpos.le]
      have hb0 : w.2 = 0 := by omega
      have hzO : zTurn w = ((0 : ℤ), (0 : ℤ)) := by
        rw [hzeq, hb0]
        norm_num
      rw [hzO]
      exact origin_mem_freeV (frameAt word)
    · -- `1 ≤ l ≤ D − 1`: the block vertex `(−b, 2l − b)` with `q ≤ n`
      have hlD' : l < D := by omega
      have hfl : (D - N) * l / D = w.2 := by
        have e : (D - N) * l = ((D - N) * l - D * w.2) + D * w.2 := by ring
        rw [e, Int.add_mul_ediv_left _ _ hDpos.ne', Int.ediv_eq_zero_of_lt hR0 (by linarith), zero_add]
      have hbc : ((frameAt word).child.den - (frameAt word).child.num) * l / (frameAt word).child.den = w.2 := by
        have hv := vBlock_floor_agree (frameAt word) l h1 (by rw [hDg]; exact hlD')
        rw [hDg, hNg] at hv
        rw [hv]
        exact hfl
      have hq : ((frameAt word).child.den - (frameAt word).child.num) * l -
          (frameAt word).child.den * (((frameAt word).child.den - (frameAt word).child.num) * l /
            (frameAt word).child.den) ≤ (frameAt word).child.num := by
        rw [hbc]
        have hid : D * (((frameAt word).child.den - (frameAt word).child.num) * l - (frameAt word).child.den * w.2) =
            (N * (frameAt word).child.den - D * (frameAt word).child.num) * l +
              (frameAt word).child.den * ((D - N) * l - D * w.2) := by
          ring
        have hm := mul_le_mul_of_nonneg_left hrle (show (0 : ℤ) ≤ (frameAt word).child.den by omega)
        rcases hεN with h2 | h2
        · rw [h2] at hid
          have hD' : D * (((frameAt word).child.den - (frameAt word).child.num) * l -
              (frameAt word).child.den * w.2) ≤ D * (frameAt word).child.num := by
            linarith
          exact le_of_mul_le_mul_left hD' hDpos
        · rw [h2] at hid
          have hD' : D * (((frameAt word).child.den - (frameAt word).child.num) * l -
              (frameAt word).child.den * w.2) ≤ D * (frameAt word).child.num := by
            linarith
          exact le_of_mul_le_mul_left hD' hDpos
      have hz : zTurn w = (-(((frameAt word).child.den - (frameAt word).child.num) * l /
          (frameAt word).child.den), 2 * l - ((frameAt word).child.den - (frameAt word).child.num) * l /
          (frameAt word).child.den) := by
        rw [hzeq, hbc]
      rw [hz]
      exact even_block_mem_freeV (frameAt word) l h1 (by rw [hDg]; exact hlD') hq

end FLatticePaper.Induction
