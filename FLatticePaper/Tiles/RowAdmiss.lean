import FLatticePaper.Tiles.RowPalin
import FLatticePaper.Tiles.AlmostTiling

/-! The two admissibility inequalities of the neighbour disjointness. For the first word `w1` in the admissible cases, the
north columns `k` and `cntI - 1 - k` sum to at most the first coordinate sum plus one (`L_g2`, the translate `T - g2`). -/

namespace FLatticePaper.Tiles

theorem colN_b (V : F2Word) (s : ℤ) :
    colN (Unit4.one :: Unit4.one :: Unit4.i :: V) (0, 0) s = 2 + (if s = 0 then 0 else colN V (0, 0) (s - 1)) := by
  rw [colN_cons_one, colN_cons_one, colN_cons_i]
  split_ifs <;> ring

theorem colN_c (V : F2Word) (s : ℤ) :
    colN (Unit4.one :: V) (0, 0) s = 1 + colN V (0, 0) s :=
  colN_cons_one V s

theorem sum_fst_b (wt : F2Word) : (F2Word.sum (Unit4.one :: Unit4.one :: Unit4.i :: (wt ++ [Unit4.one]))).1
    = (F2Word.sum wt).1 + 3 := by
  rw [sum_cons', sum_cons', sum_cons', sum_append', sum_cons', sum_nil']
  simp [Unit4.vec]
  ring

theorem cntI_b (wt : F2Word) : cntI (Unit4.one :: Unit4.one :: Unit4.i :: (wt ++ [Unit4.one]))
    = cntI wt + 1 := by
  simp [cntI, cntI_append]
  ring

theorem sum_fst_c (wt : F2Word) : (F2Word.sum (Unit4.one :: (wt ++ [Unit4.one, Unit4.one, Unit4.one]))).1
    = (F2Word.sum wt).1 + 4 := by
  simp only [sum_cons', sum_append', sum_nil', Unit4.vec, Prod.fst_add, add_zero]
  ring

theorem cntI_c (wt : F2Word) : cntI (Unit4.one :: (wt ++ [Unit4.one, Unit4.one, Unit4.one])) = cntI wt := by
  simp [cntI, cntI_append]

/-- The first admissible inequality: for an admissible word `w1` in `1` and `i`, the north columns `s` and
`cntI - 1 - s` sum to at most the first coordinate sum plus one. -/
theorem L_g2 (w1 : F2Word) (hA : Admissible w1) :
    ∀ s : ℤ, 0 ≤ s → s < cntI w1 → colN w1 (0, 0) s + colN w1 (0, 0) (cntI w1 - 1 - s) ≤ (F2Word.sum w1).1 + 1 := by
  obtain ⟨hmono, -, -, hcase⟩ := hA
  have hlet : ∀ x ∈ w1, x = .one ∨ x = .i ∨ x = .negOne := fun x hx =>
    (hmono x hx).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
  rcases hcase with hpal | ⟨wt, hw, hwt, -⟩ | ⟨wt, hw, hwt, -⟩
  · intro s hs0 hs
    have := pal_sum_aux w1.length w1 le_rfl hlet hpal s hs0 hs
    linarith
  · subst hw
    have hform : [Unit4.one, Unit4.one, Unit4.i] ++ wt ++ [Unit4.one]
        = Unit4.one :: Unit4.one :: Unit4.i :: (wt ++ [Unit4.one]) := by simp
    rw [hform] at hlet hmono ⊢
    have hwtl : ∀ x ∈ wt, x = .one ∨ x = .i := fun x hx => hmono x (by simp [hx])
    have hnn : ∀ y ∈ wt, y ≠ .negI := fun y hy => by
      rcases hwtl y hy with h | h <;> simp [h]
    have hPnn := sum_fst_nonneg wt hwtl
    have hPle : ∀ t, colN wt (0, 0) t ≤ (F2Word.sum wt).1 := fun t => colN_le_sum wt hwtl t
    intro s hs0 hs
    rw [cntI_b wt] at hs ⊢
    rw [sum_fst_b wt, colN_b, colN_b]
    have hcol : ∀ t, 0 ≤ t → t < cntI wt → colN (wt ++ [Unit4.one]) (0, 0) t = colN wt (0, 0) t := fun t ht0 ht1 =>
      colN_lo wt [Unit4.one] hnn (0, 0) t (by dsimp only; omega) (by dsimp only; omega)
    have hidx : cntI wt + 1 - 1 - s = cntI wt - s := by ring
    rw [hidx]
    split_ifs with h1 h2
    · linarith
    · have := hcol (cntI wt - s - 1) (by omega) (by omega)
      have := hPle (cntI wt - s - 1)
      have hh : (0 : ℤ) = 0 := rfl
      linarith [hcol (cntI wt - s - 1) (by omega) (by omega), hPle (cntI wt - s - 1)]
    · linarith [hcol (s - 1) (by omega) (by omega), hPle (s - 1)]
    · have hp := pal_sum_aux wt.length wt le_rfl
        (fun x hx => (hwtl x hx).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))) hwt s
        (by omega) (by omega)
      have hm := mon_one_i wt hwtl (s - 1) (by omega) (by omega)
      have e2 : s - 1 + 1 = s := by ring
      rw [e2] at hm
      have e : cntI wt - s - 1 = cntI wt - 1 - s := by ring
      have hc2 : colN wt (0, 0) (cntI wt - s - 1) = colN wt (0, 0) (cntI wt - 1 - s) := by rw [e]
      linarith [hcol (s - 1) (by omega) (by omega), hcol (cntI wt - s - 1) (by omega) (by omega)]

  · subst hw
    have hform : [Unit4.one] ++ wt ++ [Unit4.one, Unit4.one, Unit4.one]
        = Unit4.one :: (wt ++ [Unit4.one, Unit4.one, Unit4.one]) := by simp
    rw [hform] at hlet hmono ⊢
    have hV : ∀ x ∈ wt, x = .one ∨ x = .i := fun x hx => hmono x (by simp [hx])
    have hnn : ∀ y ∈ wt, y ≠ .negI := fun y hy => by
      rcases hV y hy with h | h <;> simp [h]
    have hPle : ∀ t, colN wt (0, 0) t ≤ (F2Word.sum wt).1 := fun t => colN_le_sum wt hV t
    intro s hs0 hs
    rw [cntI_c wt] at hs ⊢
    rw [sum_fst_c wt, colN_c, colN_c]
    have hcol : ∀ t, 0 ≤ t → t < cntI wt → colN (wt ++ [Unit4.one, Unit4.one, Unit4.one]) (0, 0) t
        = colN wt (0, 0) t := fun t ht0 ht1 =>
      colN_lo wt [Unit4.one, Unit4.one, Unit4.one] hnn (0, 0) t (by dsimp only; omega) (by dsimp only; omega)
    rw [hcol s hs0 hs, hcol (cntI wt - 1 - s) (by omega) (by omega)]
    have hp := pal_sum_aux wt.length wt le_rfl
      (fun x hx => (hV x hx).elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))) hwt s hs0 hs
    have e : cntI wt - 1 - s = cntI wt - 1 - s := rfl
    linarith

theorem mapMulINegI (v : F2Word) : (v.map Unit4.mulNegI).map Unit4.mulI = v := by
  induction v with
  | nil => rfl
  | cons x v ih => cases x <;> simp [Unit4.mulNegI, Unit4.mulI, ih]

theorem mulNegI_injective : Function.Injective Unit4.mulNegI := by
  intro a b h
  cases a <;> cases b <;> simp_all [Unit4.mulNegI, Unit4.mulI]

theorem colN_iii_zero (j : ℤ) (h0 : 0 ≤ j) (h2 : j ≤ 2) :
    colN [Unit4.i, Unit4.i, Unit4.i] (0, 0) j = 0 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp [colN_cons_i]

theorem colN_iii (p : GInt) (k : ℤ) (h0 : p.2 ≤ k) (h2 : k ≤ p.2 + 2) :
    colN [Unit4.i, Unit4.i, Unit4.i] p k = p.1 := by
  rw [colN_trans, colN_iii_zero (k - p.2) (by omega) (by omega)]
  ring

theorem mon3 (w : F2Word) (hw : ∀ x ∈ w, x = .i ∨ x = .negOne) (t : ℤ) (h0 : 0 ≤ t) (h3 : t + 3 < cntI w) :
    colN w (0, 0) (t + 3) ≤ colN w (0, 0) t := by
  have a1 : colN w (0, 0) (t + 1) ≤ colN w (0, 0) t := mon_i_neg w hw t h0 (by omega)
  have a2 : colN w (0, 0) (t + 2) ≤ colN w (0, 0) (t + 1) := by
    have := mon_i_neg w hw (t + 1) (by omega) (by omega)
    rwa [show t + 1 + 1 = t + 2 by ring] at this
  have a3 : colN w (0, 0) (t + 3) ≤ colN w (0, 0) (t + 2) := by
    have := mon_i_neg w hw (t + 2) (by omega) (by omega)
    rwa [show t + 2 + 1 = t + 3 by ring] at this
  linarith

/-- The second admissible inequality: for an admissible word `u` in `1` and `i`, the word `w2` with `w2.map mulNegI = u`
has north columns `h` and `cntI w2 - h` summing to at most its first coordinate sum. -/
theorem L_g1 (w2 : F2Word) (hA : Admissible (w2.map Unit4.mulNegI)) (hlet : ∀ x ∈ w2, x = .i ∨ x = .negOne) :
    ∀ h : ℤ, 1 ≤ h → h ≤ cntI w2 - 1 →
      colN w2 (0, 0) h + colN w2 (0, 0) (cntI w2 - h) ≤ (F2Word.sum w2).1 := by
  obtain ⟨hmono, -, -, hcase⟩ := hA
  rcases hcase with hpal | ⟨ut, hut, hutp, -⟩ | ⟨ut, hut, hutp, -⟩
  · have hw2p : w2.reverse = w2 := by
      have h1 : (w2.reverse).map Unit4.mulNegI = w2.map Unit4.mulNegI := by
        simpa [List.map_reverse] using hpal
      exact List.map_injective_iff.mpr mulNegI_injective h1
    have hl3 : ∀ x ∈ w2, x = .one ∨ x = .i ∨ x = .negOne := fun x hx =>
      (hlet x hx).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
    intro h h1 h2
    have hp := pal_sum_aux w2.length w2 le_rfl hl3 hw2p (h - 1) (by omega) (by omega)
    have hm := mon_i_neg w2 hlet (h - 1) (by omega) (by omega)
    have e1 : cntI w2 - 1 - (h - 1) = cntI w2 - h := by ring
    have e2 : h - 1 + 1 = h := by ring
    rw [e1] at hp
    rw [e2] at hm
    linarith
  · have hutl : ∀ y ∈ ut, y = .one ∨ y = .i := fun y hy =>
      hmono y (by rw [hut]; simp [hy])
    have hWl : ∀ x ∈ ut.map Unit4.mulI, x = .i ∨ x = .negOne := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases hutl y hy with rfl | rfl <;> simp [Unit4.mulI]
    have hWp : (ut.map Unit4.mulI).reverse = ut.map Unit4.mulI := by
      rw [← List.map_reverse, hutp]
    have hw2 : w2 = Unit4.i :: Unit4.i :: Unit4.negOne :: (ut.map Unit4.mulI ++ [Unit4.i]) := by
      rw [← mapMulINegI w2, hut]
      simp [Unit4.mulI]
    subst hw2
    have hnnW : ∀ y ∈ ut.map Unit4.mulI, y ≠ .negI := fun y hy => by
      rcases hWl y hy with h | h <;> simp [h]
    have hRW : cntI (Unit4.i :: Unit4.i :: Unit4.negOne :: (ut.map Unit4.mulI ++ [Unit4.i]))
        = cntI (ut.map Unit4.mulI) + 3 := by
      simp [cntI, cntI_append]; ring
    have hSW : (F2Word.sum (Unit4.i :: Unit4.i :: Unit4.negOne :: (ut.map Unit4.mulI ++ [Unit4.i]))).1
        = (F2Word.sum (ut.map Unit4.mulI)).1 - 1 := by
      simp only [sum_cons', sum_append', sum_nil', Unit4.vec, Prod.fst_add, add_zero]
      ring
    have hPal := fun t ht0 ht1 => pal_sum_aux (ut.map Unit4.mulI).length (ut.map Unit4.mulI) le_rfl
      (fun x hx => (hWl x hx).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))) hWp t ht0 ht1
    have hXlo : ∀ t, 0 ≤ t → t < cntI (ut.map Unit4.mulI) → colN (ut.map Unit4.mulI ++ [Unit4.i]) (0, 0) t
        = colN (ut.map Unit4.mulI) (0, 0) t := fun t ht0 ht1 =>
      colN_lo _ [Unit4.i] hnnW (0, 0) t (by dsimp only; omega) (by dsimp only; omega)
    have hXhi : colN (ut.map Unit4.mulI ++ [Unit4.i]) (0, 0) (cntI (ut.map Unit4.mulI))
        = (F2Word.sum (ut.map Unit4.mulI)).1 := by
      rw [colN_hi _ [Unit4.i] hnnW (0, 0) (cntI (ut.map Unit4.mulI)) (by simp), colN_single_i]
      simp
    have hf1 : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (ut.map Unit4.mulI ++ [Unit4.i])) (0, 0) 1 = 0 := by
      rw [colN_cons_i, if_neg (by norm_num)]
      simp [colN_cons_i]
    have hft : ∀ t, 2 ≤ t → colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (ut.map Unit4.mulI ++ [Unit4.i])) (0, 0) t
        = -1 + colN (ut.map Unit4.mulI ++ [Unit4.i]) (0, 0) (t - 2) := by
      intro t ht
      rw [colN_cons_i, if_neg (by omega), colN_cons_i, if_neg (by omega), colN_cons_negOne,
        show t - 1 - 1 = t - 2 by ring]
    intro h hh1 hh2
    rw [hRW] at hh2 ⊢
    rw [hSW]
    have hRn := cntI_nonneg (ut.map Unit4.mulI)
    rcases (show h = 1 ∨ h = cntI (ut.map Unit4.mulI) + 2 ∨
        (2 ≤ h ∧ h ≤ cntI (ut.map Unit4.mulI) + 1) by omega) with h1 | h2 | ⟨hm1, hm2⟩
    · rw [h1, hf1, show cntI (ut.map Unit4.mulI) + 3 - 1 = cntI (ut.map Unit4.mulI) + 2 by ring,
        hft _ (by omega), show cntI (ut.map Unit4.mulI) + 2 - 2 = cntI (ut.map Unit4.mulI) by ring, hXhi]
      linarith
    · rw [h2, show cntI (ut.map Unit4.mulI) + 3 - (cntI (ut.map Unit4.mulI) + 2) = 1 by ring, hf1,
        hft _ (by omega), show cntI (ut.map Unit4.mulI) + 2 - 2 = cntI (ut.map Unit4.mulI) by ring, hXhi]
      linarith
    · rw [hft h hm1, hft _ (by omega),
        show cntI (ut.map Unit4.mulI) + 3 - h - 2 = cntI (ut.map Unit4.mulI) + 1 - h by ring,
        hXlo (h - 2) (by omega) (by omega), hXlo (cntI (ut.map Unit4.mulI) + 1 - h) (by omega) (by omega)]
      have hp := hPal (h - 2) (by omega) (by omega)
      have e : cntI (ut.map Unit4.mulI) - 1 - (h - 2) = cntI (ut.map Unit4.mulI) + 1 - h := by ring
      rw [e] at hp
      linarith
  · have hutl : ∀ y ∈ ut, y = .one ∨ y = .i := fun y hy =>
      hmono y (by rw [hut]; simp [hy])
    have hWl : ∀ x ∈ ut.map Unit4.mulI, x = .i ∨ x = .negOne := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases hutl y hy with rfl | rfl <;> simp [Unit4.mulI]
    have hWp : (ut.map Unit4.mulI).reverse = ut.map Unit4.mulI := by
      rw [← List.map_reverse, hutp]
    have hw2 : w2 = Unit4.i :: (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]) := by
      rw [← mapMulINegI w2, hut]
      simp [Unit4.mulI]
    subst hw2
    have hnnW : ∀ y ∈ ut.map Unit4.mulI, y ≠ .negI := fun y hy => by
      rcases hWl y hy with h | h <;> simp [h]
    have hRW : cntI (Unit4.i :: (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]))
        = cntI (ut.map Unit4.mulI) + 4 := by
      simp [cntI, cntI_append]; ring
    have hSW : (F2Word.sum (Unit4.i :: (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]))).1
        = (F2Word.sum (ut.map Unit4.mulI)).1 := by
      simp only [sum_cons', sum_append', sum_nil', Unit4.vec, Prod.fst_add, add_zero]
      simp
    have hPal := fun t ht0 ht1 => pal_sum_aux (ut.map Unit4.mulI).length (ut.map Unit4.mulI) le_rfl
      (fun x hx => (hWl x hx).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))) hWp t ht0 ht1
    have hsnd : (F2Word.sum (ut.map Unit4.mulI)).2 = cntI (ut.map Unit4.mulI) := sum_snd _ hnnW
    have hYlo : ∀ t, 0 ≤ t → t < cntI (ut.map Unit4.mulI) →
        colN (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) t = colN (ut.map Unit4.mulI) (0, 0) t :=
      fun t ht0 ht1 => colN_lo _ [Unit4.i, Unit4.i, Unit4.i] hnnW (0, 0) t (by dsimp only; omega) (by dsimp only; omega)
    have hYhi : ∀ t, cntI (ut.map Unit4.mulI) ≤ t → t ≤ cntI (ut.map Unit4.mulI) + 2 →
        colN (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) t = (F2Word.sum (ut.map Unit4.mulI)).1 := by
      intro t ht0 ht1
      rw [colN_hi _ [Unit4.i, Unit4.i, Unit4.i] hnnW (0, 0) t (by simp; omega)]
      have hp2 : ((0, 0) + F2Word.sum (ut.map Unit4.mulI) : GInt).2 = cntI (ut.map Unit4.mulI) := by
        rw [Prod.snd_add, hsnd]
        simp
      rw [colN_iii _ t (by rw [hp2]; omega) (by rw [hp2]; omega)]
      simp
    have hfpos : ∀ t, colN (Unit4.i :: (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) t
        = if t = 0 then 0 else colN (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (t - 1) :=
      fun t => colN_cons_i _ t
    have hl : ∀ x ∈ Unit4.i :: (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]), x = .i ∨ x = .negOne := by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h' | h'
        · exact hWl x h'
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
          rcases h' with rfl | rfl | rfl <;> simp
    have hnp : ∀ t, colN (Unit4.i :: (ut.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) t ≤ 0 :=
      fun t => colN_nonpos _ hl t
    intro h hh1 hh2
    have hRn := cntI_nonneg (ut.map Unit4.mulI)
    rw [hRW] at hh2 ⊢
    rw [hSW]
    by_cases hA : cntI (ut.map Unit4.mulI) + 1 ≤ h
    · rw [hfpos h, if_neg (show ¬ (h = 0) by omega),
        hYhi (h - 1) (by omega) (by omega)]
      linarith [hnp (cntI (ut.map Unit4.mulI) + 4 - h)]
    · by_cases hB : h ≤ 3
      · rw [hfpos (cntI (ut.map Unit4.mulI) + 4 - h), if_neg (show ¬ (cntI (ut.map Unit4.mulI) + 4 - h = 0) by omega),
          show cntI (ut.map Unit4.mulI) + 4 - h - 1 = cntI (ut.map Unit4.mulI) + 3 - h by ring,
          hYhi (cntI (ut.map Unit4.mulI) + 3 - h) (by omega) (by omega)]
        linarith [hnp h]
      · rw [hfpos h, if_neg (show ¬ (h = 0) by omega), hfpos (cntI (ut.map Unit4.mulI) + 4 - h),
          if_neg (show ¬ (cntI (ut.map Unit4.mulI) + 4 - h = 0) by omega),
          show cntI (ut.map Unit4.mulI) + 4 - h - 1 = cntI (ut.map Unit4.mulI) + 3 - h by ring,
          hYlo (h - 1) (by omega) (by omega), hYlo (cntI (ut.map Unit4.mulI) + 3 - h) (by omega) (by omega)]
        have hp := hPal (h - 1) (by omega) (by omega)
        have e : cntI (ut.map Unit4.mulI) - 1 - (h - 1) = cntI (ut.map Unit4.mulI) - h := by ring
        rw [e] at hp
        have hm := mon3 (ut.map Unit4.mulI) hWl (cntI (ut.map Unit4.mulI) - h) (by omega) (by omega)
        have e' : cntI (ut.map Unit4.mulI) - h + 3 = cntI (ut.map Unit4.mulI) + 3 - h := by ring
        rw [e'] at hm
        linarith

end FLatticePaper.Tiles
