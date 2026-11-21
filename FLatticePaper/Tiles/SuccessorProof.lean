import FLatticePaper.Tiles.SuccessorCover
import FLatticePaper.Tiles.RowOverlap
import FLatticePaper.Tiles.WordFacts1
import FLatticePaper.Tiles.WordFacts3

/-! The successor condition `SuccCover`, proved from the row overlap of an edge-connected tile and the column facts of
the admissible words. For a right end `(N_t + 1, c.2 + t)` the witnesses are: the translate `-g2` on the rows `t+r-1`
(bottom, `t ≤ q`) and `t+r` (top, palindromic `w1`); the tile itself on row `t+1` (top, `w1` not palindromic); the
translate `g1` on rows `t-q` (top, `t ≥ q`) and `s-1` (bottom, `t > q`); and the tile itself on row `t-1` (bottom,
`t > q`, when the `w2` column drops). -/

namespace FLatticePaper.Tiles

theorem w2_cntI_pos {w2 : F2Word} (hA2 : Admissible (w2.map Unit4.mulNegI)) : 1 ≤ cntI w2 := by
  obtain ⟨-, hhead, -, -⟩ := hA2
  cases w2 with
  | nil => simp at hhead
  | cons x w2' =>
    have hn := cntI_nonneg w2'
    cases x <;> simp [Unit4.mulNegI, Unit4.mulI, cntI] at hhead ⊢
    all_goals omega

theorem wNrowLt {c : GInt} {w1 w2 : F2Word} {j : ℤ} (h : j < cntI w1) :
    Nrow c w1 w2 j = c.1 + colN w1 (0, 0) j := by
  unfold Nrow; rw [if_pos h]

theorem wNrowGe {c : GInt} {w1 w2 : F2Word} {j : ℤ} (h : cntI w1 ≤ j) :
    Nrow c w1 w2 j = c.1 + ((F2Word.sum w1).1 + colN w2 (0, 0) (j - cntI w1)) := by
  unfold Nrow; rw [if_neg (not_lt.mpr h)]

theorem wSrowLt {c : GInt} {w1 w2 : F2Word} {j : ℤ} (h : j < cntI w2) :
    Srow c w1 w2 j = c.1 + ((F2Word.sum w2).1 - colN w2 (0, 0) (cntI w2 - 1 - j)) := by
  unfold Srow; rw [if_pos h]

theorem wSrowGe {c : GInt} {w1 w2 : F2Word} {j : ℤ} (h : cntI w2 ≤ j) :
    Srow c w1 w2 j = c.1 + ((F2Word.sum w1).1 + (F2Word.sum w2).1
      - colN w1 (0, 0) (cntI w1 + cntI w2 - 1 - j)) := by
  unfold Srow; rw [if_neg (not_lt.mpr h), sum_append_fst]

/-- Non-decreasing north columns of a word in `1` and `i`. -/
theorem colN_mono_le (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) (a : ℤ) (ha : 0 ≤ a) :
    ∀ n : ℕ, a + n < cntI u → colN u (0, 0) a ≤ colN u (0, 0) (a + n) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by push_cast at hn; omega)
    have h2 := mon_one_i u hu (a + n) (by omega) (by push_cast at hn; omega)
    have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
    rw [e]; linarith

theorem colN_mono_le' (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < cntI u) : colN u (0, 0) a ≤ colN u (0, 0) b := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst hn
  exact colN_mono_le u hu a ha n hb

/-- Non-increasing north columns of a word in `i` and `-1`. -/
theorem colN_anti_le (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) (a : ℤ) (ha : 0 ≤ a) :
    ∀ n : ℕ, a + n < cntI u → colN u (0, 0) (a + n) ≤ colN u (0, 0) a := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by push_cast at hn; omega)
    have h2 := mon_i_neg u hu (a + n) (by omega) (by push_cast at hn; omega)
    have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
    rw [e]; linarith

theorem colN_anti_le' (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < cntI u) : colN u (0, 0) b ≤ colN u (0, 0) a := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst hn
  exact colN_anti_le u hu a ha n hb

theorem sum_w1_pos {w1 : F2Word} (hA1 : Admissible w1) : 1 ≤ (F2Word.sum w1).1 := by
  have hhead := hA1.2.1
  cases w1 with
  | nil => simp at hhead
  | cons x v =>
    have hx : x = .one := by simpa using hhead
    subst hx
    have := sum_fst_nonneg v (fun y hy => hA1.1 y (List.mem_cons_of_mem _ hy))
    rw [sum_cons']
    simp [Unit4.vec]
    linarith

theorem w2_c0 {w2 : F2Word} (hA2 : Admissible (w2.map Unit4.mulNegI)) (hq : 0 < cntI w2) :
    colN w2 (0, 0) 0 = 0 := by
  have hhead := hA2.2.1
  cases w2 with
  | nil => simp [cntI] at hq
  | cons x v =>
    have hx : x = .i := by
      cases x <;> simp [Unit4.mulNegI, Unit4.mulI] at hhead ⊢
    subst hx
    rw [colN_cons_i]; simp

theorem c1_le_N0 {c : GInt} {w1 w2 : F2Word} (_hA1 : Admissible w1) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) (hr : 1 ≤ cntI w2) : c.1 ≤ Nrow c w1 w2 0 := by
  have hq0 := cntI_nonneg w1
  by_cases hq : 0 < cntI w1
  · rw [wNrowLt hq]
    have := colN_nonneg w1 h1 0
    linarith
  · have hq0 : cntI w1 = 0 := by have := cntI_nonneg w1; omega
    rw [wNrowGe (j := 0) (by omega)]
    have hc : colN w2 (0, 0) (0 - cntI w1) = 0 := by
      rw [hq0, show (0 : ℤ) - 0 = 0 by ring]
      exact w2_c0 hA2 (by omega)
    have := sum_fst_nonneg w1 h1
    rw [hc]
    linarith

theorem XN_le {c : GInt} {w1 w2 : F2Word} (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) {t j : ℤ} (ht : 0 ≤ t) (htj : t ≤ j) (htq : t ≤ cntI w1)
    (hj : j < cntI w1 + cntI w2) : Nrow c w1 w2 t + (F2Word.sum w2).1 ≤ Nrow c w1 w2 j := by
  have hq0 := cntI_nonneg w1
  have hr0 := cntI_nonneg w2
  have hX : (F2Word.sum w2).1 ≤ 0 := sum_fst_nonpos w2 h2
  by_cases hjq : j < cntI w1
  · have ht' : t < cntI w1 := by omega
    rw [wNrowLt ht', wNrowLt hjq]
    have := colN_mono_le' w1 h1 t j ht htj hjq
    linarith
  · rw [wNrowGe (not_lt.mp hjq)]
    have hNt : Nrow c w1 w2 t ≤ c.1 + (F2Word.sum w1).1 := by
      by_cases htq' : t < cntI w1
      · rw [wNrowLt htq']
        have := colN_le_sum w1 h1 t
        linarith
      · rw [wNrowGe (j := t) (by omega)]
        have := colN_nonpos w2 h2 (t - cntI w1)
        linarith
    have hXlo := sum_fst_le_colN_neg w2 h2 (j - cntI w1) (by omega) (by omega)
    linarith

theorem cov_bot_zero {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) {t : ℤ}
    (hA : InRow c w1 w2 (t - 1) (Nrow c w1 w2 t + 1)) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t) :=
  cov_row1 (j := t - 1) hT h1 h2 (latticeOf_zero _ _) (by simpa using hA)
    (by simp only [Prod.snd_zero, sub_zero]; ring)

theorem cov_bot_g1 {T : CellTile} {c : GInt} {w1 w2 : F2Word} (hn1 : ∀ x ∈ w1, x ≠ .negI)
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) {t : ℤ}
    (hA : InRow c w1 w2 (t - cntI w1 - 1) (Nrow c w1 w2 t + 1 - (F2Word.sum w1).1)) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t) := by
  refine cov_row0 (j := t - cntI w1 - 1) hT h1 h2 (u := almostV₁ w1) ?_ ?_ ?_
  · exact ⟨1, 0, by ext <;> simp⟩
  · rw [almostV₁_eq w1 hn1]; simpa using hA
  · rw [almostV₁_eq w1 hn1]; dsimp only; ring

/-- The bottom right end for `t ≤ q`: the translate `-g2` covers it through the row `t + r - 1`. -/
theorem bot_le {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) (hr : 1 ≤ cntI w2)
    (hn1 : ∀ x ∈ w1, x ≠ .negI) (hn2 : ∀ x ∈ w2, x ≠ .negI)
    {t : ℤ} (ht0 : 0 ≤ t) (htq : t ≤ cntI w1) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t) := by
  have hq0 := cntI_nonneg w1
  have hr0 := cntI_nonneg w2
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hA2.1 x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  apply cov_bot_negG2 hT h1 h2 hn1 hn2 (t := t)
  refine ⟨by omega, by omega, ?_, XN_le h1 h2 ht0 (by omega) htq (by omega)⟩
  rcases (show t = 0 ∨ (1 ≤ t ∧ t < cntI w1) ∨ (1 ≤ t ∧ t = cntI w1) by omega) with h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst h0
    rw [wSrowLt (j := 0 + cntI w2 - 1) (by omega), show cntI w2 - 1 - (0 + cntI w2 - 1) = 0 by ring]
    have hc0 := w2_c0 hA2 (by omega)
    rw [hc0]
    have := c1_le_N0 (c := c) hA1 h1 hA2 hr
    linarith
  · rw [wSrowGe (j := t + cntI w2 - 1) (by omega),
      show cntI w1 + cntI w2 - 1 - (t + cntI w2 - 1) = cntI w1 - t by ring]
    rw [wNrowLt hb]
    have := adm_A2 hA1 (t := t) ha (by omega)
    linarith
  · subst hb
    rw [wSrowGe (j := cntI w1 + cntI w2 - 1) (by omega),
      show cntI w1 + cntI w2 - 1 - (cntI w1 + cntI w2 - 1) = 0 by ring]
    rw [wNrowGe (j := cntI w1) (by omega), show cntI w1 - cntI w1 = 0 by ring, w2_c0 hA2 (by omega)]
    have := colN_nonneg w1 h1 0
    linarith

/-- A north column of `w2` plus one lies below the upper end of a row at which the column is taken to the right. -/
theorem c1_add_le_Nrow {c : GInt} {w1 w2 : F2Word} (hA1 : Admissible w1)
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) {j k : ℤ} (hj0 : 0 ≤ j)
    (_hjQ : j < cntI w1 + cntI w2) (_hk0 : 0 ≤ k) (hkr : k < cntI w2) (hjk : j - cntI w1 ≤ k) :
    colN w2 (0, 0) k + 1 + c.1 ≤ Nrow c w1 w2 j := by
  have hq0 := cntI_nonneg w1
  have hr0 := cntI_nonneg w2
  by_cases hjq : j < cntI w1
  · rw [wNrowLt hjq]
    have hq : 0 < cntI w1 := by omega
    have h0 := adm_head_colN hA1 hq
    have hm := colN_mono_le' w1 h1 0 j le_rfl hj0 hjq
    have hn := colN_nonpos w2 h2 k
    linarith
  · rw [wNrowGe (not_lt.mp hjq)]
    have hP := sum_w1_pos hA1
    have hc := colN_anti_le' w2 h2 (j - cntI w1) k (by omega) hjk hkr
    linarith

/-- The bottom right end for `t > q`: the tile itself (on row `t-1`) when the column of `w2` drops, the translate
`g1` (on row `t-q-1`) when it does not. -/
theorem bot_gt {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hE : EdgeConnected T) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI))
    (hn1 : ∀ x ∈ w1, x ≠ .negI) (_hn2 : ∀ x ∈ w2, x ≠ .negI)
    {t : ℤ} (htq : cntI w1 < t) (htQ : t < cntI w1 + cntI w2) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t) := by
  have hq0 := cntI_nonneg w1
  have hr0 := cntI_nonneg w2
  have hr : 1 ≤ cntI w2 := w2_cntI_pos hA2
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hA2.1 x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  have hsr : t - cntI w1 < cntI w2 := by omega
  have hanti := colN_anti_le' w2 h2 (t - cntI w1 - 1) (t - cntI w1) (by omega) (by omega) hsr
  rcases eq_or_lt_of_le hanti with heq | hlt
  · -- the column does not drop: the translate g1 covers
    apply cov_bot_g1 hn1 hT h1 h2 (t := t)
    have hw := w2_D hA2 (s := t - cntI w1 - 1) (by omega) (by omega)
    have hadd := c1_add_le_Nrow (c := c) hA1 h1 h2 (j := t - cntI w1 - 1) (k := t - cntI w1) (by omega) (by omega)
      (by omega) hsr (by omega)
    have hNt : Nrow c w1 w2 t = c.1 + ((F2Word.sum w1).1 + colN w2 (0, 0) (t - cntI w1)) :=
      wNrowGe (j := t) (by omega)
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [wSrowLt (j := t - cntI w1 - 1) (by omega)]
      linarith [hw, heq]
    · linarith [hNt, hadd, heq]
  · -- the column drops: the tile itself covers
    apply cov_bot_zero hT h1 h2 (t := t)
    have hov := row_overlap hT hE h1 h2 (t := t - 1) (by omega) (by omega)
    rw [show t - 1 + 1 = t by ring] at hov
    have hNt : Nrow c w1 w2 t = c.1 + ((F2Word.sum w1).1 + colN w2 (0, 0) (t - cntI w1)) :=
      wNrowGe (j := t) (by omega)
    have hNt1 : Nrow c w1 w2 (t - 1) = c.1 + ((F2Word.sum w1).1 + colN w2 (0, 0) (t - 1 - cntI w1)) :=
      wNrowGe (j := t - 1) (by omega)
    have hlt' : colN w2 (0, 0) (t - cntI w1) + 1 ≤ colN w2 (0, 0) (t - 1 - cntI w1) := by
      rw [show t - 1 - cntI w1 = t - cntI w1 - 1 by ring]; exact hlt
    refine ⟨by omega, by omega, ?_, ?_⟩
    · linarith [hov.2]
    · linarith

/-- The upper right end when `t < q` and `w1` is a palindrome: the translate `-g2` covers it through the row `t + r`. -/
theorem top_lt_pal {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) (hpal : w1.reverse = w1)
    (hn1 : ∀ x ∈ w1, x ≠ .negI) (hn2 : ∀ x ∈ w2, x ≠ .negI)
    {t : ℤ} (ht0 : 0 ≤ t) (htq : t < cntI w1) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t + 1) := by
  have hq0 := cntI_nonneg w1
  have hr : 1 ≤ cntI w2 := w2_cntI_pos hA2
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hA2.1 x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  apply cov_top_negG2 hT h1 h2 hn1 hn2 (t := t)
  refine ⟨by omega, by omega, ?_, XN_le h1 h2 ht0 (by omega) (by omega) (by omega)⟩
  rw [wSrowGe (j := t + cntI w2) (by omega),
    show cntI w1 + cntI w2 - 1 - (t + cntI w2) = cntI w1 - 1 - t by ring]
  rw [wNrowLt htq]
  have hp := adm_pal_sum hA1.1 hpal (s := t) ht0 htq
  linarith

/-- The upper right end when `t < q` and `w1` is not a palindrome: the tile itself covers it on row `t + 1`. -/
theorem top_lt_nonpal {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hE : EdgeConnected T) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI)) (hnp : w1.reverse ≠ w1)
    {t : ℤ} (ht0 : 0 ≤ t) (htq : t < cntI w1) (htQ : t + 1 < cntI w1 + cntI w2) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t + 1) := by
  have hq0 := cntI_nonneg w1
  have hr : 1 ≤ cntI w2 := w2_cntI_pos hA2
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hA2.1 x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  have hov := row_overlap hT hE h1 h2 (t := t) ht0 htQ
  refine cov_top_zero (L := latticeOf (almostV₁ w1) (almostV₂ w2)) (latticeOf_zero _ _) hT h1 h2 (t := t) ?_
  refine ⟨by omega, htQ, ?_, ?_⟩
  · linarith [hov.1]
  · rcases (show t + 1 < cntI w1 ∨ t + 1 = cntI w1 by omega) with hlt | heq
    · rw [wNrowLt hlt, wNrowLt htq]
      have := adm_strict hA1 hnp ht0 (by omega)
      linarith
    · rw [wNrowLt htq, wNrowGe (j := t + 1) (by omega), show t + 1 - cntI w1 = 0 by omega, w2_c0 hA2 (by omega)]
      have := adm_last_colN hA1 ht0 htq
      linarith

/-- The upper right end when `t ≥ q`: the translate `g1` covers it through the row `t - q`. -/
theorem top_ge {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hA1 : Admissible w1)
    (hA2 : Admissible (w2.map Unit4.mulNegI))
    (hn1 : ∀ x ∈ w1, x ≠ .negI) (_hn2 : ∀ x ∈ w2, x ≠ .negI)
    {t : ℤ} (htq : cntI w1 ≤ t) (htQ : t < cntI w1 + cntI w2) :
    Cov T (latticeOf (almostV₁ w1) (almostV₂ w2)) (Nrow c w1 w2 t + 1, c.2 + t + 1) := by
  have hq0 := cntI_nonneg w1
  have hr : 1 ≤ cntI w2 := w2_cntI_pos hA2
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hA2.1 x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  apply cov_top_g1 hT h1 h2 hn1 (t := t)
  have hw := w2_D hA2 (s := t - cntI w1) (by omega) (by omega)
  have hadd := c1_add_le_Nrow (c := c) hA1 h1 h2 (j := t - cntI w1) (k := t - cntI w1) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hNt : Nrow c w1 w2 t = c.1 + ((F2Word.sum w1).1 + colN w2 (0, 0) (t - cntI w1)) :=
    wNrowGe (j := t) (by omega)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [wSrowLt (j := t - cntI w1) (by omega)]
    linarith [hw, hNt]
  · linarith [hNt, hadd]

/-- The successor condition: every right end of a row of an edge-connected admissible tile is covered. -/
theorem succCover_proved {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2)) (hE : EdgeConnected T)
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) :
    SuccCover c w1 w2 T (latticeOf (almostV₁ w1) (almostV₂ w2)) := by
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hA2.1 x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  have hn1 : ∀ x ∈ w1, x ≠ .negI := fun x hx => by rcases h1 x hx with h | h <;> simp [h]
  have hn2 : ∀ x ∈ w2, x ≠ .negI := fun x hx => by rcases h2 x hx with h | h <;> simp [h]
  have hr : 1 ≤ cntI w2 := w2_cntI_pos hA2
  intro t ht0 htQ
  refine ⟨?_, ?_⟩
  · by_cases htq : t ≤ cntI w1
    · exact bot_le hT hA1 hA2 hr hn1 hn2 ht0 htq
    · exact bot_gt hT hE hA1 hA2 hn1 hn2 (by omega) htQ
  · by_cases htq : t < cntI w1
    · by_cases hpal : w1.reverse = w1
      · exact top_lt_pal hT hA1 hA2 hpal hn1 hn2 ht0 htq
      · exact top_lt_nonpal hT hE hA1 hA2 hpal ht0 htq (by omega)
    · exact top_ge hT hA1 hA2 hn1 hn2 (by omega) htQ

end FLatticePaper.Tiles
