import FLatticePaper.Tiles.WordFacts2

/-! The lower bound `c_s + c_{r-1-s} ≥ X_2 - 1` for the north columns of `w2`, in the three admissibility classes of
`w2' = w2.map mulNegI`: the palindrome (equality), the case b `w2 = i i (-1) w̃ i`, and the case c `w2 = i w̃ i i i`. -/

namespace FLatticePaper.Tiles

theorem nf_mono {k k' : ℕ} {u : F2Word} (h : NFollowedBy k u) (hk : k' ≤ k) : NFollowedBy k' u := by
  intro j hj m hm
  exact h j hj m (by omega)

theorem nf_of_map_mulI {k : ℕ} {w' : F2Word} (h : IFollowedBy k w') : NFollowedBy k (w'.map Unit4.mulI) := by
  intro j hj m hm
  rw [List.getElem?_map] at hj
  have hx : w'[j]? = some .i := by
    cases h' : w'[j]? with
    | none => simp [h'] at hj
    | some x =>
      rw [h'] at hj
      cases x <;> simp [Unit4.mulI] at hj ⊢
  have h2 := h j hx m hm
  rw [List.getElem?_map, h2]
  rfl

/-- The case b with palindrome `w̃`: the north columns of `i i (-1) w̃ i` satisfy the lower bound. -/
theorem D_b (wt : F2Word) (hp : wt.reverse = wt) (hl : ∀ x ∈ wt, x = .i ∨ x = .negOne) {s : ℤ}
    (hs0 : 0 ≤ s) (hs : s < cntI (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i]))) :
    (F2Word.sum (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i]))).1 - 1 ≤
      colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) s +
      colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0)
        (cntI (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) - 1 - s) := by
  have hnI : ∀ x ∈ wt, x ≠ .negI := fun x hx => by rcases hl x hx with h | h <;> simp [h]
  have hmono : ∀ x ∈ wt ++ [Unit4.i], x = .i ∨ x = .negOne := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hl x h
    · simp at h; exact Or.inl h
  have hm0 : 0 ≤ cntI wt := cntI_nonneg wt
  have hcntW : cntI (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) = cntI wt + 3 := by
    simp [cntI, cntI_append]; ring
  have hsumW : (F2Word.sum (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i]))).1
      = (F2Word.sum wt).1 - 1 := by
    simp [sum_cons', sum_append', sum_nil', Unit4.vec]; ring
  rw [hcntW] at hs ⊢
  rw [hsumW]
  set m := cntI wt with hm
  set Xt := (F2Word.sum wt).1 with hXt
  clear_value m Xt
  have hcntV : cntI (wt ++ [Unit4.i]) = m + 1 := by simp [cntI_append, cntI, hm]
  -- values of the north columns of the word
  have hW0 : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) 0 = 0 := by
    rw [colN_cons_i]; simp
  have hW1 : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) 1 = 0 := by
    rw [colN_cons_i]; simp [colN_cons_i]
  have hWge : ∀ j : ℤ, 2 ≤ j → colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) j
      = -1 + colN (wt ++ [Unit4.i]) (0, 0) (j - 2) := by
    intro j hj
    rw [colN_cons_i, if_neg (by omega), colN_cons_i, if_neg (by omega), colN_cons_negOne,
      show j - 1 - 1 = j - 2 by ring]
  -- values of the column function on `wt ++ [i]`
  have hVlt : ∀ k : ℤ, 0 ≤ k → k < m → colN (wt ++ [Unit4.i]) (0, 0) k = colN wt (0, 0) k :=
    fun k h0 h1 => colN_lo wt [Unit4.i] hnI (0, 0) k (by simp; omega) (by simp; omega)
  have hVm : colN (wt ++ [Unit4.i]) (0, 0) m = Xt := by
    rw [colN_hi wt [Unit4.i] hnI (0, 0) m (by simp [hm])]
    simp [colN_single_i, hXt]
  have hpal : ∀ a : ℤ, 0 ≤ a → a < m → colN wt (0, 0) a + colN wt (0, 0) (m - 1 - a) = Xt := fun a h0 h1 => by
    have := pal_sum_aux wt.length wt le_rfl (fun x hx => by
      rcases hl x hx with h | h <;> simp [h]) hp a h0 (by rw [← hm]; exact h1)
    rw [← hXt, ← hm] at this
    exact this
  have hmonV : ∀ k : ℤ, 0 ≤ k → k + 1 < m + 1 → colN (wt ++ [Unit4.i]) (0, 0) (k + 1)
      ≤ colN (wt ++ [Unit4.i]) (0, 0) k := fun k h0 h1 =>
    mon_i_neg (wt ++ [Unit4.i]) hmono k h0 (by rw [hcntV]; exact h1)
  have hXt0 : Xt ≤ 0 := by have := sum_fst_nonpos wt hl; rw [← hXt] at this; exact this
  have hXtlo : ∀ k : ℤ, 0 ≤ k → k < m → Xt ≤ colN wt (0, 0) k := fun k h0 h1 => by
    have := sum_fst_le_colN_neg wt hl k h0 (by rw [← hm]; exact h1)
    rw [← hXt] at this
    exact this
  -- the value at index m+1 is at least Xt - 1
  have hWm1 : Xt - 1 ≤ colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 1) := by
    rcases (show m = 0 ∨ 1 ≤ m by omega) with h0 | h1
    · rw [show m + 1 = 1 by omega, hW1]; linarith
    · rw [hWge (m + 1) (by omega), show m + 1 - 2 = m - 1 by ring]
      have := hVlt (m - 1) (by omega) (by omega)
      have := hXtlo (m - 1) (by omega) (by omega)
      linarith
  have hsymW : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 2)
      = -1 + Xt := by rw [hWge (m + 2) (by omega)]; congr 1; rw [show m + 2 - 2 = m by ring]; exact hVm
  rcases (show s = 0 ∨ s = 1 ∨ (2 ≤ s ∧ s ≤ m) ∨ s = m + 1 ∨ s = m + 2 by omega) with h | h | ⟨h2, h3⟩ | h | h
  · subst h
    have hx : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 3 - 1 - 0)
        = -1 + Xt := by rw [show m + 3 - 1 - 0 = m + 2 by ring]; exact hsymW
    linarith
  · subst h
    have hx : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 3 - 1 - 1)
        = colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 1) := by
      congr 1; ring
    linarith
  · have hsA : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) s
        = -1 + colN (wt ++ [Unit4.i]) (0, 0) (s - 2) := hWge s (by omega)
    have hsB : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 3 - 1 - s)
        = -1 + colN (wt ++ [Unit4.i]) (0, 0) (m - s) := by
      rw [hWge _ (by omega), show m + 3 - 1 - s - 2 = m - s by ring]
    have hmon := hmonV (m - s) (by omega) (by omega)
    have e1 := hVlt (s - 2) (by omega) (by omega)
    have e2 := hVlt (m - s + 1) (by omega) (by omega)
    have hp2 := hpal (s - 2) (by omega) (by omega)
    rw [show m - 1 - (s - 2) = m - s + 1 by ring] at hp2
    rw [hsA, hsB]
    linarith
  · subst h
    have hx : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 3 - 1 - (m + 1))
        = 0 := by
      rw [show m + 3 - 1 - (m + 1) = 1 by ring]; exact hW1
    linarith
  · subst h
    have hx : colN (Unit4.i :: Unit4.i :: Unit4.negOne :: (wt ++ [Unit4.i])) (0, 0) (m + 3 - 1 - (m + 2))
        = 0 := by
      rw [show m + 3 - 1 - (m + 2) = 0 by ring]; exact hW0
    linarith

/-- The case c with palindrome `w̃`: the north columns of `i w̃ i i i` satisfy the lower bound. -/
theorem D_c (wt : F2Word) (hp : wt.reverse = wt) (hl : ∀ x ∈ wt, x = .i ∨ x = .negOne)
    (hN : NFollowedBy 2 (wt ++ [Unit4.i, Unit4.i, Unit4.i])) {s : ℤ} (hs0 : 0 ≤ s)
    (hs : s < cntI (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i]))) :
    (F2Word.sum (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i]))).1 - 1 ≤
      colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) s +
      colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0)
        (cntI (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) - 1 - s) := by
  have hnI : ∀ x ∈ wt, x ≠ .negI := fun x hx => by rcases hl x hx with h | h <;> simp [h]
  have hmono : ∀ x ∈ wt ++ [Unit4.i, Unit4.i, Unit4.i], x = .i ∨ x = .negOne := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hl x h
    · simp at h; exact Or.inl h
  have hm0 : 0 ≤ cntI wt := cntI_nonneg wt
  have hcntW : cntI (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) = cntI wt + 4 := by
    simp [cntI, cntI_append]; ring
  have hsumW : (F2Word.sum (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i]))).1 = (F2Word.sum wt).1 := by
    simp [sum_cons', sum_append', sum_nil', Unit4.vec]
  rw [hcntW] at hs ⊢
  rw [hsumW]
  set m := cntI wt with hm
  set Xt := (F2Word.sum wt).1 with hXt
  clear_value m Xt
  have hWz : colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) 0 = 0 := by
    rw [colN_cons_i]; simp
  have hWp : ∀ j : ℤ, 1 ≤ j → colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) j
      = colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (j - 1) := by
    intro j hj
    rw [colN_cons_i, if_neg (by omega)]
  have hVlt : ∀ k : ℤ, 0 ≤ k → k < m → colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) k
      = colN wt (0, 0) k :=
    fun k h0 h1 => colN_lo wt [Unit4.i, Unit4.i, Unit4.i] hnI (0, 0) k (by simp; omega) (by simp; omega)
  have hsnd : ((0, 0) + F2Word.sum wt : GInt).2 = m := by simp [sum_snd wt hnI, hm]
  have hVm : ∀ k : ℤ, m ≤ k → k ≤ m + 2 → colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) k = Xt := by
    intro k h0 h2
    rw [colN_hi wt [Unit4.i, Unit4.i, Unit4.i] hnI (0, 0) k (by simp; omega),
      colN_iii _ k (by rw [hsnd]; exact h0) (by rw [hsnd]; omega)]
    simp [hXt]
  have hpal : ∀ a : ℤ, 0 ≤ a → a < m → colN wt (0, 0) a + colN wt (0, 0) (m - 1 - a) = Xt := fun a h0 h1 => by
    have := pal_sum_aux wt.length wt le_rfl (fun x hx => by
      rcases hl x hx with h | h <;> simp [h]) hp a h0 (by rw [← hm]; exact h1)
    rw [← hXt, ← hm] at this
    exact this
  have hVl : ∀ x ∈ wt ++ [Unit4.i, Unit4.i, Unit4.i], x = .i ∨ x = .negOne := hmono
  have hcntV : cntI (wt ++ [Unit4.i, Unit4.i, Unit4.i]) = m + 3 := by simp [cntI_append, cntI, hm]
  -- the case s = 0 and s = m + 3
  rcases (show s = 0 ∨ (1 ≤ s ∧ s ≤ m + 2) ∨ s = m + 3 by omega) with h | ⟨h1, h2⟩ | h
  · subst h
    have hx : colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) (m + 4 - 1 - 0) = Xt := by
      rw [hWp _ (by omega), show m + 4 - 1 - 0 - 1 = m + 2 by ring]
      exact hVm _ (by omega) le_rfl
    linarith
  · have hA : colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) s
        = colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (s - 1) := hWp s h1
    have hB : colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) (m + 4 - 1 - s)
        = colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (m + 2 - s) := by
      rw [hWp _ (by omega), show m + 4 - 1 - s - 1 = m + 2 - s by ring]
    rw [hA, hB]
    rcases (show s ≤ 2 ∨ m + 1 ≤ s ∨ 3 ≤ s ∧ s ≤ m by omega) with h3 | h3 | ⟨h3, h4⟩
    · -- the first north columns, with the partner in the trailing `i`s
      have hb : colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (m + 2 - s) = Xt :=
        hVm _ (by omega) (by omega)
      have ha : -1 ≤ colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (s - 1) := by
        rcases (show s - 1 = 0 ∨ s - 1 = 1 by omega) with h5 | h5
        · rw [h5]; exact nf_colN_zero hVl hN (by omega)
        · rw [h5]; exact nf_colN_one hVl hN (by omega)
      linarith
    · have ha : colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (s - 1) = Xt :=
        hVm _ (by omega) (by omega)
      have hb : -1 ≤ colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (m + 2 - s) := by
        rcases (show m + 2 - s = 0 ∨ m + 2 - s = 1 by omega) with h5 | h5
        · rw [h5]; exact nf_colN_zero hVl hN (by omega)
        · rw [h5]; exact nf_colN_one hVl hN (by omega)
      linarith
    · have hg := gapN2 (wt ++ [Unit4.i, Unit4.i, Unit4.i]) hVl hN (s - 3) (by omega)
        (by rw [hcntV]; omega)
      have hvA : colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (s - 1)
          = colN wt (0, 0) (s - 1) := hVlt _ (by omega) (by omega)
      have hvB : colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (m + 2 - s)
          = colN wt (0, 0) (m + 2 - s) := hVlt _ (by omega) (by omega)
      have hvC : colN (wt ++ [Unit4.i, Unit4.i, Unit4.i]) (0, 0) (s - 3)
          = colN wt (0, 0) (s - 3) := hVlt _ (by omega) (by omega)
      have hpl := hpal (s - 3) (by omega) (by omega)
      rw [show m - 1 - (s - 3) = m + 2 - s by ring] at hpl
      rw [show s - 3 + 2 = s - 1 by ring] at hg
      linarith
  · subst h
    have hx : colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) (m + 4 - 1 - (m + 3)) = 0 := by
      rw [show m + 4 - 1 - (m + 3) = 0 by ring]; exact hWz
    have hy : colN (Unit4.i :: (wt ++ [Unit4.i, Unit4.i, Unit4.i])) (0, 0) (m + 3)
        = Xt := by
      rw [hWp _ (by omega), show m + 3 - 1 = m + 2 by ring]
      exact hVm _ (by omega) le_rfl
    linarith

/-- The lower bound `c_s + c_{r-1-s} ≥ X_2 - 1` for the north columns of `w2`, in each admissibility class of
`w2.map mulNegI`. -/
theorem w2_D {w2 : F2Word} (hA : Admissible (w2.map Unit4.mulNegI)) {s : ℤ} (hs0 : 0 ≤ s) (hs : s < cntI w2) :
    (F2Word.sum w2).1 - 1 ≤ colN w2 (0, 0) s + colN w2 (0, 0) (cntI w2 - 1 - s) := by
  obtain ⟨w', hw'⟩ : ∃ w', w' = w2.map Unit4.mulNegI := ⟨_, rfl⟩
  have hw2 : w2 = w'.map Unit4.mulI := by rw [hw', mapMulINegI]
  rw [← hw'] at hA
  subst hw2
  have hl' : ∀ x ∈ w', x = .one ∨ x = .i := hA.1
  rcases hA.2.2.2 with hpal | ⟨wt', hw, hwt, hifol⟩ | ⟨wt', hw, hwt, hifol⟩
  · have hp : (w'.map Unit4.mulI).reverse = w'.map Unit4.mulI := by rw [← List.map_reverse, hpal]
    have hlet : ∀ x ∈ w'.map Unit4.mulI, x = .one ∨ x = .i ∨ x = .negOne := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases hl' y hy with rfl | rfl <;> simp [Unit4.mulI]
    have := pal_sum_aux _ (w'.map Unit4.mulI) le_rfl hlet hp s hs0 hs
    linarith
  · subst hw
    have hWeq : (([Unit4.one, Unit4.one, Unit4.i] ++ wt' ++ [Unit4.one] : F2Word).map Unit4.mulI)
        = Unit4.i :: Unit4.i :: Unit4.negOne :: (wt'.map Unit4.mulI ++ [Unit4.i]) := by
      simp [List.map_append, Unit4.mulI]
    rw [hWeq] at hs ⊢
    have hwtp : (wt'.map Unit4.mulI).reverse = wt'.map Unit4.mulI := by rw [← List.map_reverse, hwt]
    have hwtl : ∀ x ∈ wt'.map Unit4.mulI, x = .i ∨ x = .negOne := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases hl' y (by simp [hy]) with rfl | rfl <;> simp [Unit4.mulI]
    exact D_b _ hwtp hwtl hs0 hs
  · subst hw
    have hWeq : (([Unit4.one] ++ wt' ++ [Unit4.one, Unit4.one, Unit4.one] : F2Word).map Unit4.mulI)
        = Unit4.i :: (wt'.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]) := by
      simp [List.map_append, Unit4.mulI]
    rw [hWeq] at hs ⊢
    have hwtp : (wt'.map Unit4.mulI).reverse = wt'.map Unit4.mulI := by rw [← List.map_reverse, hwt]
    have hwtl : ∀ x ∈ wt'.map Unit4.mulI, x = .i ∨ x = .negOne := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases hl' y (by simp [hy]) with rfl | rfl <;> simp [Unit4.mulI]
    have hN : NFollowedBy 2 (wt'.map Unit4.mulI ++ [Unit4.i, Unit4.i, Unit4.i]) := by
      have h3 := nf_of_map_mulI hifol
      rw [hWeq] at h3
      exact nf_mono (nf_tail h3) (by norm_num)
    exact D_c _ hwtp hwtl hN hs0 hs

end FLatticePaper.Tiles
