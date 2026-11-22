import FLatticePaper.Tiles.ArcRows
import FLatticePaper.Tiles.RowCols

/-! Task 53, arc lemma. The boundary word `boundaryWordOf w1 w2 = w1 ++ w2 ++ w1.map neg ++ w2.map neg` (the forward
convention of the repository) is a four-arc loop: `w1` in `{1, i}`, `w2` in `{i, -1}`. Let `U = w1 ++ w2`,
`F h = colN U 0 h` the column of the north step at height `h`, and `H = (sum U).2`. Then the right end of row `b` is
`F b` and the left end is `(sum U).1 - F (H - 1 - b)` (`arc_left_eq`). The row inequalities reduce to one inequality:
`a + s2 + 1 ≤ F q + F r` whenever `q + r` is within one of `H - 1`, where `a = (sum w1).1`, `s2 = (sum w2).1`. It holds
under the sum inequalities `(sum w1).2 < (sum w2).2` and `0 < a + s2`, and the corner condition
`¬(w1 starts with i ∧ w2 ends with i)`. -/

namespace FLatticePaper.Tiles

theorem arc_ne_negI_one_i (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) : ∀ x ∈ u, x ≠ .negI :=
  fun x hx => by
    rcases hu x hx with rfl | rfl <;> decide

theorem arc_ne_negI_i_negOne (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) : ∀ x ∈ u, x ≠ .negI :=
  fun x hx => by
    rcases hu x hx with rfl | rfl <;> decide

theorem arc_sum_append (a b : F2Word) : F2Word.sum (a ++ b) = F2Word.sum a + F2Word.sum b := by
  simp [F2Word.sum, List.map_append, List.sum_append]

theorem arc_sum_cons (x : Unit4) (u : F2Word) : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by
  simp [F2Word.sum]

theorem arc_zero_add (x : GInt) : ((0 : ℤ), (0 : ℤ)) + x = x := by
  simp

theorem arc_colN_cons_one (u : F2Word) (s : ℤ) : colN (.one :: u) (0, 0) s = 1 + colN u (0, 0) s := by
  have e : colN (.one :: u) (0, 0) s = colN u (1, 0) s := by
    simp [colN, Unit4.vec]
  rw [e, colN_trans u (1, 0) s]
  simp

theorem arc_colN_cons_negOne (u : F2Word) (s : ℤ) :
    colN (.negOne :: u) (0, 0) s = -1 + colN u (0, 0) s := by
  have e : colN (.negOne :: u) (0, 0) s = colN u (-1, 0) s := by
    simp [colN, Unit4.vec]
  rw [e, colN_trans u (-1, 0) s]
  simp

theorem arc_colN_cons_i_pos (u : F2Word) (s : ℤ) (h : (0 : ℤ) = s) : colN (.i :: u) (0, 0) s = 0 := by
  subst h
  simp [colN]

theorem arc_colN_cons_i_neg (u : F2Word) (s : ℤ) (h : ¬ (0 : ℤ) = s) :
    colN (.i :: u) (0, 0) s = colN u (0, 0) (s - 1) := by
  have e : colN (.i :: u) (0, 0) s = colN u (0, 1) s := by
    simp [colN, Unit4.vec, h]
  rw [e, colN_trans u (0, 1) s]
  simp

theorem arc_colN_nonneg (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) (s : ℤ) : 0 ≤ colN u (0, 0) s := by
  induction u generalizing s with
  | nil => simp [colN]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rcases hx with rfl | rfl
    · rw [arc_colN_cons_one]
      have := ih hu' s
      omega
    · by_cases h0 : (0 : ℤ) = s
      · simp only [arc_colN_cons_i_pos u s h0, le_refl]
      · rw [arc_colN_cons_i_neg u s h0]
        exact ih hu' (s - 1)

theorem arc_sum_fst_nonpos (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) : (F2Word.sum u).1 ≤ 0 := by
  induction u with
  | nil => simp [F2Word.sum]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rw [arc_sum_cons, Prod.fst_add]
    rcases hx with rfl | rfl <;> simp [Unit4.vec] <;> linarith [ih hu']

theorem arc_colN_ge_sum (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) (s : ℤ) :
    (F2Word.sum u).1 ≤ colN u (0, 0) s := by
  induction u generalizing s with
  | nil => simp [colN, F2Word.sum]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hnp := arc_sum_fst_nonpos u hu'
    rcases hx with rfl | rfl
    · have hv : (Unit4.vec .i).1 = 0 := rfl
      rw [arc_sum_cons, Prod.fst_add, hv, zero_add]
      by_cases h0 : (0 : ℤ) = s
      · rw [arc_colN_cons_i_pos u s h0]
        exact hnp
      · rw [arc_colN_cons_i_neg u s h0]
        have := ih hu' (s - 1)
        omega
    · have hv : (Unit4.vec .negOne).1 = -1 := rfl
      rw [arc_sum_cons, Prod.fst_add, hv, arc_colN_cons_negOne]
      have := ih hu' s
      omega

theorem arc_last_i (w : F2Word) (hw : ∀ x ∈ w, x = .i ∨ x = .negOne) (g : ℤ) (hg0 : 0 ≤ g)
    (hg1 : g < cntI w) (hle : colN w (0, 0) g ≤ (F2Word.sum w).1) : w.getLast? = some .i := by
  rcases List.eq_nil_or_concat w with h | ⟨u, y, rfl⟩
  · subst h
    simp [cntI] at hg1
    omega
  · simp only [List.concat_eq_append] at hle hg1 ⊢
    have hy : y = .i ∨ y = .negOne := hw y (by simp)
    have hu : ∀ x ∈ u, x = .i ∨ x = .negOne := fun x hx => hw x (by simp [hx])
    rcases hy with rfl | rfl
    · simp
    · exfalso
      have hcnt : cntI (u ++ [Unit4.negOne]) = cntI u := by
        simp [cntI_append, cntI]
      have hlo : colN (u ++ [Unit4.negOne]) (0, 0) g = colN u (0, 0) g := by
        apply colN_lo u [Unit4.negOne] (arc_ne_negI_i_negOne u hu) (0, 0) g
        · simpa using hg0
        · simp only [zero_add]
          rw [hcnt] at hg1
          exact hg1
      have hneg : F2Word.sum [Unit4.negOne] = (-1, 0) := by
        simp [F2Word.sum, Unit4.vec]
      have hsum : (F2Word.sum (u ++ [Unit4.negOne])).1 = (F2Word.sum u).1 - 1 := by
        rw [arc_sum_append, hneg, Prod.fst_add]
        show (F2Word.sum u).1 + (-1 : ℤ) = (F2Word.sum u).1 - 1
        ring
      have hge := arc_colN_ge_sum u hu g
      rw [hlo, hsum] at hle
      omega

theorem arc_F_lo (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (s : ℤ) (hs0 : 0 ≤ s)
    (hs1 : s < cntI w1) : colN (w1 ++ w2) (0, 0) s = colN w1 (0, 0) s := by
  apply colN_lo w1 w2 (arc_ne_negI_one_i w1 h1) (0, 0) s
  · simpa using hs0
  · simpa using hs1

theorem arc_F_hi (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (s : ℤ) (hs : cntI w1 ≤ s) :
    colN (w1 ++ w2) (0, 0) s = (F2Word.sum w1).1 + colN w2 (0, 0) (s - cntI w1) := by
  have hne := arc_ne_negI_one_i w1 h1
  have e := colN_hi w1 w2 hne (0, 0) s (by simpa using hs)
  have c1 : (F2Word.sum w1).2 = cntI w1 := sum_snd w1 hne
  rw [e, colN_trans w2 ((0, 0) + F2Word.sum w1) s, arc_zero_add, c1]

/-- The mixed case of the key inequality: one index below the height of `w1`, one above. -/
theorem arc_mixed (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hc : ¬ (w1.head? = some .i ∧ w2.getLast? = some .i)) (q r : ℤ) (hq0 : 0 ≤ q) (hq1 : q < cntI w1)
    (hr1 : cntI w1 ≤ r) (hr2 : r < cntI w1 + cntI w2) :
    (F2Word.sum w1).1 + (F2Word.sum w2).1 + 1 ≤ colN (w1 ++ w2) (0, 0) q + colN (w1 ++ w2) (0, 0) r := by
  rw [arc_F_lo w1 w2 h1 q hq0 hq1, arc_F_hi w1 w2 h1 r hr1]
  by_contra hcon
  rw [not_le] at hcon
  have hnn := arc_colN_nonneg w1 h1 q
  have hlow := arc_colN_ge_sum w2 h2 (r - cntI w1)
  have hw1zero : colN w1 (0, 0) q = 0 := by
    omega
  have hw2 : colN w2 (0, 0) (r - cntI w1) ≤ (F2Word.sum w2).1 := by
    omega
  have hhead : w1.head? = some .i := by
    cases w1 with
    | nil => simp [cntI] at hq1; omega
    | cons x u =>
      rcases h1 x (List.mem_cons_self ..) with rfl | rfl
      · exfalso
        have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => h1 y (List.mem_cons_of_mem _ hy)
        rw [arc_colN_cons_one] at hw1zero
        have := arc_colN_nonneg u hu' q
        omega
      · rfl
  have hlast : w2.getLast? = some .i :=
    arc_last_i w2 h2 (r - cntI w1) (by omega) (by omega) hw2
  exact hc ⟨hhead, hlast⟩

/-- The key inequality for `F h = colN (w1 ++ w2) 0 h`. -/
theorem arc_key (w1 w2 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn : (F2Word.sum w1).2 < (F2Word.sum w2).2) (ha : 0 < (F2Word.sum w1).1 + (F2Word.sum w2).1)
    (hc : ¬ (w1.head? = some .i ∧ w2.getLast? = some .i)) {q r : ℤ}
    (hq0 : 0 ≤ q) (hq1 : q < (F2Word.sum w1).2 + (F2Word.sum w2).2)
    (hr0 : 0 ≤ r) (hr1 : r < (F2Word.sum w1).2 + (F2Word.sum w2).2)
    (hs1 : (F2Word.sum w1).2 + (F2Word.sum w2).2 - 2 ≤ q + r)
    (hs2 : q + r ≤ (F2Word.sum w1).2 + (F2Word.sum w2).2) :
    (F2Word.sum w1).1 + (F2Word.sum w2).1 + 1 ≤ colN (w1 ++ w2) (0, 0) q + colN (w1 ++ w2) (0, 0) r := by
  have hn1 : cntI w1 = (F2Word.sum w1).2 := (sum_snd w1 (arc_ne_negI_one_i w1 h1)).symm
  have hn2 : cntI w2 = (F2Word.sum w2).2 := (sum_snd w2 (arc_ne_negI_i_negOne w2 h2)).symm
  rw [← hn1, ← hn2] at hn hq1 hr1 hs1 hs2
  rcases lt_or_ge q (cntI w1) with hq | hq <;> rcases lt_or_ge r (cntI w1) with hr | hr
  · exfalso
    omega
  · exact arc_mixed w1 w2 h1 h2 hc q r hq0 hq hr hr1
  · have := arc_mixed w1 w2 h1 h2 hc r q hr0 hr hq hq1
    omega
  · rw [arc_F_hi w1 w2 h1 q hq, arc_F_hi w1 w2 h1 r hr]
    have hcq := arc_colN_ge_sum w2 h2 (q - cntI w1)
    have hcr := arc_colN_ge_sum w2 h2 (r - cntI w1)
    omega

/-- The left end of row `b` of the four-arc loop. -/
theorem arc_left_eq (w1 w2 : F2Word) (b : ℤ) :
    arcLeft w1 w2 (0, 0) b =
      (F2Word.sum (w1 ++ w2)).1 - colN (w1 ++ w2) (0, 0) ((F2Word.sum (w1 ++ w2)).2 - 1 - b) := by
  unfold arcLeft
  rw [← List.map_append, arc_zero_add, colS_trans, colS_map_neg]
  have e : -(b - (F2Word.sum (w1 ++ w2)).2) - 1 = (F2Word.sum (w1 ++ w2)).2 - 1 - b := by ring
  rw [e]
  ring

/-- The row inequalities of the four-arc loop: each row is nonempty and consecutive rows overlap. -/
theorem cellRowChain_of_arc_inequalities (T : CellTile) (w1 w2 : F2Word)
    (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn : (F2Word.sum w1).2 < (F2Word.sum w2).2) (ha : 0 < (F2Word.sum w1).1 + (F2Word.sum w2).1)
    (hc : ¬ (w1.head? = some .i ∧ w2.getLast? = some .i)) : CellRowChain T := by
  have hne1 := arc_ne_negI_one_i w1 h1
  have hne2 := arc_ne_negI_i_negOne w2 h2
  have hU1 : (F2Word.sum (w1 ++ w2)).1 = (F2Word.sum w1).1 + (F2Word.sum w2).1 := by
    rw [arc_sum_append, Prod.fst_add]
  have hU2 : (F2Word.sum (w1 ++ w2)).2 = (F2Word.sum w1).2 + (F2Word.sum w2).2 := by
    rw [arc_sum_append, Prod.snd_add]
  have c1 : (F2Word.sum w1).2 = cntI w1 := sum_snd w1 hne1
  have c2 : (F2Word.sum w2).2 = cntI w2 := sum_snd w2 hne2
  have hcnt : cntI (w1 ++ w2) = (F2Word.sum w1).2 + (F2Word.sum w2).2 := by
    rw [cntI_append, c1, c2]
  apply cellRowChain_of_arcs hT h1 h2
  · intro b hb0 hb1
    have hb0' : 0 ≤ b := by simpa using hb0
    have hb1' : b < (F2Word.sum w1).2 + (F2Word.sum w2).2 := by
      have : b < cntI (w1 ++ w2) := by simpa using hb1
      rwa [hcnt] at this
    show arcLeft w1 w2 (0, 0) b < arcRight w1 w2 (0, 0) b
    rw [arc_left_eq, hU1, hU2]
    show _ < colN (w1 ++ w2) (0, 0) b
    have := arc_key w1 w2 h1 h2 hn ha hc (q := b) (r := (F2Word.sum w1).2 + (F2Word.sum w2).2 - 1 - b)
      hb0' hb1' (by omega) (by omega) (by omega) (by omega)
    omega
  · intro b hb0 hb1
    have hb0' : 0 ≤ b := by simpa using hb0
    have hb1' : b + 1 < (F2Word.sum w1).2 + (F2Word.sum w2).2 := by
      have : b + 1 < cntI (w1 ++ w2) := by simpa using hb1
      rwa [hcnt] at this
    constructor
    · show arcLeft w1 w2 (0, 0) (b + 1) < arcRight w1 w2 (0, 0) b
      rw [arc_left_eq, hU1, hU2]
      show _ < colN (w1 ++ w2) (0, 0) b
      have := arc_key w1 w2 h1 h2 hn ha hc (q := b)
        (r := (F2Word.sum w1).2 + (F2Word.sum w2).2 - 1 - (b + 1))
        hb0' (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · show arcLeft w1 w2 (0, 0) b < arcRight w1 w2 (0, 0) (b + 1)
      rw [arc_left_eq, hU1, hU2]
      show _ < colN (w1 ++ w2) (0, 0) (b + 1)
      have := arc_key w1 w2 h1 h2 hn ha hc (q := b + 1)
        (r := (F2Word.sum w1).2 + (F2Word.sum w2).2 - 1 - b)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      omega

end FLatticePaper.Tiles
