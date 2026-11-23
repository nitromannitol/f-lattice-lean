import FLatticePaper.Tiles.NeighbourDisjoint
import FLatticePaper.Tiles.SuccessorProof

/-! Task 50, part 2 (Q10): the row inequalities of the packing of `lemma:almost_square_tiling`.

The rows of the tile are the intervals `[Srow t, Nrow t)` (`mem_iff_nr`). This file proves the two slope bounds of the rows,
`Nrow (t + B + 1) ≤ Nrow t + A` and `Nrow t ≤ Nrow (t + D) + C` (with `B = cntI w1`, `D = cntI w2`, `A = (sum w1).1`,
`C = -(sum w2).1`), from the column ranges alone, and the first admissible row inequality `L_g1` (the interface inequality of the
word `-i w2`) as the row inequality of the translate by `v1 = (A, B + 1)`. The induction over the multiples of the two translates
is in `PackRows`. -/

namespace FLatticePaper.Tiles

/-- The first coordinate sum of a word with letters `1, i` is nonnegative. -/
theorem sum_fst_nonneg_of_one_i : ∀ u : F2Word, (∀ x ∈ u, x = .one ∨ x = .i) → 0 ≤ (F2Word.sum u).1
  | [], _ => by simp [F2Word.sum]
  | x :: u, h => by
    have hx := h x (List.mem_cons_self ..)
    have hu := sum_fst_nonneg_of_one_i u (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have e : F2Word.sum (x :: u) = Unit4.vec x + F2Word.sum u := by simp [F2Word.sum]
    rw [e, Prod.fst_add]
    rcases hx with rfl | rfl <;> simp [Unit4.vec] <;> omega

/-- The first coordinate sum of a word with letters `i, -1` is nonpositive. -/
theorem sum_fst_nonpos_of_i_negOne : ∀ u : F2Word, (∀ x ∈ u, x = .i ∨ x = .negOne) → (F2Word.sum u).1 ≤ 0
  | [], _ => by simp [F2Word.sum]
  | x :: u, h => by
    have hx := h x (List.mem_cons_self ..)
    have hu := sum_fst_nonpos_of_i_negOne u (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have e : F2Word.sum (x :: u) = Unit4.vec x + F2Word.sum u := by simp [F2Word.sum]
    rw [e, Prod.fst_add]
    rcases hx with rfl | rfl <;> simp [Unit4.vec] <;> omega

/-- The north column of a word with letters `i, -1` is at least the first coordinate sum (the walk moves only west). -/
theorem colN_ge_sum_of_i_negOne : ∀ (u : F2Word) (p : GInt) (b : ℤ), (∀ x ∈ u, x = .i ∨ x = .negOne) →
    p.1 + (F2Word.sum u).1 ≤ colN u p b
  | [], p, b, _ => by simp [colN, F2Word.sum]
  | x :: u, p, b, h => by
    have hx := h x (List.mem_cons_self ..)
    have hu : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hs := sum_fst_nonpos_of_i_negOne u hu
    have e : F2Word.sum (x :: u) = Unit4.vec x + F2Word.sum u := by simp [F2Word.sum]
    have ih := colN_ge_sum_of_i_negOne u (p + Unit4.vec x) b hu
    rw [Prod.fst_add] at ih
    rw [e, Prod.fst_add, colN]
    by_cases hc : x = .i ∧ p.2 = b
    · rw [if_pos hc]
      obtain ⟨rfl, -⟩ := hc
      have h0 : (Unit4.vec Unit4.i).1 = 0 := rfl
      rw [h0]
      linarith
    · rw [if_neg hc]
      linarith

variable {w1 w2 : F2Word}

/-- The north end of a row is at most the first coordinate sum of `w1` (above the lower-left column). -/
theorem Nrow_le_A (c : GInt) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (t : ℤ) :
    Nrow c w1 w2 t ≤ c.1 + (F2Word.sum w1).1 :=
  Nrow_le c w1 w2 h1 h2 t

/-- Slope bound along `v1`: the north end rises by at most `A` over `B + 1` rows. -/
theorem Nrow_slope_v1 (c : GInt) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (s : ℤ) (hs : 0 ≤ s) (hL : s + cntI w1 + 1 < cntI w1 + cntI w2) :
    Nrow c w1 w2 (s + cntI w1 + 1) ≤ Nrow c w1 w2 s + (F2Word.sum w1).1 := by
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  have hA := sum_fst_nonneg_of_one_i w1 h1
  have hnn := colN_nonneg w1 h1 s
  have hnp := colN_nonpos w2 h2 (s + 1)
  have e : s + cntI w1 + 1 - cntI w1 = s + 1 := by ring
  unfold Nrow
  by_cases hsB : s < cntI w1
  · rw [if_pos hsB, if_neg (by omega), e]
    linarith
  · rw [if_neg hsB, if_neg (by omega), e]
    have hm := colN_anti_le' w2 h2 (s - cntI w1) (s + 1) (by omega) (by omega) (by omega)
    linarith

/-- Slope bound along `v2`: the north end at row `s` is at most that at row `s + D` less `C`. -/
theorem Nrow_slope_v2 (c : GInt) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (s : ℤ) (hs : 0 ≤ s) (hL : s + cntI w2 < cntI w1 + cntI w2) :
    Nrow c w1 w2 s ≤ Nrow c w1 w2 (s + cntI w2) - (F2Word.sum w2).1 := by
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  have hC := sum_fst_nonpos_of_i_negOne w2 h2
  have hge : (F2Word.sum w2).1 ≤ colN w2 (0, 0) (s + cntI w2 - cntI w1) := by
    simpa using colN_ge_sum_of_i_negOne w2 (0, 0) (s + cntI w2 - cntI w1) h2
  have hle1 := colN_le_sum w1 h1 s
  have hnp := colN_nonpos w2 h2 (s - cntI w1)
  unfold Nrow
  by_cases hb : s + cntI w2 < cntI w1
  · have hm := colN_mono_le' w1 h1 s (s + cntI w2) hs (by omega) hb
    rw [if_pos (show s < cntI w1 by omega), if_pos hb]
    linarith
  · rw [if_neg hb]
    by_cases ha : s < cntI w1
    · rw [if_pos ha]
      linarith
    · rw [if_neg ha]
      linarith

/-- The first admissible row inequality (`L_g1`, the interface of `-i w2`): the row `t` against the row `t - (B + 1)`
translated by `A`. This is the row inequality of `disj_g1`. -/
theorem row_v1_base (c : GInt) (w1' w2' : F2Word) (hA2 : Admissible (w2'.map Unit4.mulNegI)) (hlet : ∀ x ∈ w2', x = .i ∨ x = .negOne)
    (t : ℤ) (ht0 : cntI w1' + 1 ≤ t) (ht1 : t < cntI w1' + cntI w2') :
    Nrow c w1' w2' t ≤ Srow c w1' w2' (t - (cntI w1' + 1)) + (F2Word.sum w1').1 := by
  have hq := cntI_nonneg w1'
  have hr := cntI_nonneg w2'
  unfold Nrow Srow
  rw [if_neg (by omega), if_pos (by omega)]
  have key := L_g1 w2' hA2 hlet (t - cntI w1') (by omega) (by omega)
  rw [show cntI w2' - 1 - (t - (cntI w1' + 1)) = cntI w2' - (t - cntI w1') by ring]
  linarith


/-- The row inequality of the translates by `k v1`, `k ≥ 1` (the translate of the tile to the right, by the slope bound and
the first row inequality). -/
theorem row_v1_iter (c : GInt) {w1 w2 : F2Word} (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (hA2 : Admissible (w2.map Unit4.mulNegI)) (k : ℕ) (hk : 1 ≤ k) :
    ∀ t : ℤ, 0 ≤ t - (k : ℤ) * (cntI w1 + 1) → t < cntI w1 + cntI w2 →
      Nrow c w1 w2 t ≤ Srow c w1 w2 (t - (k : ℤ) * (cntI w1 + 1)) + (k : ℤ) * (F2Word.sum w1).1 := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro t ht0 ht1
    have hB : cntI w1 + 1 ≤ t := by
      have : (((1 : ℕ) : ℤ)) = 1 := by norm_num
      rw [this, one_mul] at ht0
      linarith
    have key := row_v1_base c w1 w2 hA2 h2 t hB ht1
    have hk1 : ((1 : ℕ) : ℤ) = 1 := by norm_num
    rw [hk1, one_mul, one_mul]
    exact key
  | succ n hn ih =>
    intro t ht0 ht1
    have hq := cntI_nonneg w1
    have hr := cntI_nonneg w2
    push_cast at ht0 ⊢
    have e1 : t - (cntI w1 + 1) - (n : ℤ) * (cntI w1 + 1) = t - ((n : ℤ) + 1) * (cntI w1 + 1) := by ring
    have hnn : (0 : ℤ) ≤ (n : ℤ) := by positivity
    have hs0 : 0 ≤ t - (cntI w1 + 1) := by nlinarith
    have hS := Nrow_slope_v1 c h1 h2 (t - (cntI w1 + 1)) hs0 (by linarith)
    rw [show t - (cntI w1 + 1) + cntI w1 + 1 = t by ring] at hS
    have ih' := ih (t - (cntI w1 + 1)) (by rw [e1]; exact ht0) (by linarith)
    rw [e1] at ih'
    have hA' : ((n : ℤ) + 1) * (F2Word.sum w1).1 = (n : ℤ) * (F2Word.sum w1).1 + (F2Word.sum w1).1 := by ring
    rw [hA']
    linarith

end FLatticePaper.Tiles
