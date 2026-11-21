import FLatticePaper.Tiles.RowCols

/-! Palindromes and monotonicity of the north columns from the origin: the column of the `k`-th north step, of a palindrome
in the letters `1`, `i`, `-1`, has its partner column summing to the first coordinate sum. -/

namespace FLatticePaper.Tiles

theorem colN_cons_one (v : F2Word) (s : ℤ) : colN (Unit4.one :: v) (0, 0) s = 1 + colN v (0, 0) s := by
  simp only [colN]
  rw [colN_trans v ((0, 0) + Unit4.vec .one) s]
  simp [Unit4.vec]

theorem colN_cons_negOne (v : F2Word) (s : ℤ) :
    colN (Unit4.negOne :: v) (0, 0) s = -1 + colN v (0, 0) s := by
  simp only [colN]
  rw [colN_trans v ((0, 0) + Unit4.vec .negOne) s]
  simp [Unit4.vec]

theorem colN_cons_i (v : F2Word) (s : ℤ) :
    colN (Unit4.i :: v) (0, 0) s = if s = 0 then 0 else colN v (0, 0) (s - 1) := by
  simp only [colN]
  rw [colN_trans v ((0, 0) + Unit4.vec .i) s]
  by_cases hs : s = 0
  · subst hs; simp
  · have hs' : ¬ ((0 : ℤ) = s) := fun h => hs h.symm
    rw [if_neg (fun h => hs' h.2), if_neg hs]
    simp [Unit4.vec]

/-- The north columns of words in `1` and `i` are nonnegative. -/
theorem colN_nonneg (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) (s : ℤ) : 0 ≤ colN u (0, 0) s := by
  induction u generalizing s with
  | nil => simp [colN]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rcases hx with rfl | rfl
    · rw [colN_cons_one]; linarith [ih hu' s]
    · rw [colN_cons_i]
      by_cases hs : s = 0
      · simp [hs]
      · rw [if_neg hs]; exact ih hu' (s - 1)

/-- Monotonicity of the north columns of a word in `1` and `i`: the column does not decrease from one north step to the
next. -/
theorem mon_one_i (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) :
    ∀ s : ℤ, 0 ≤ s → s + 1 < cntI u → colN u (0, 0) s ≤ colN u (0, 0) (s + 1) := by
  induction u with
  | nil => intro s _ h; simp [cntI] at h; omega
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    intro s hs0 hs1
    rcases hx with rfl | rfl
    · have hc : cntI (Unit4.one :: u) = cntI u := by simp [cntI]
      rw [hc] at hs1
      rw [colN_cons_one, colN_cons_one]
      linarith [ih hu' s hs0 hs1]
    · have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at hs1
      rw [colN_cons_i, colN_cons_i]
      by_cases h0 : s = 0
      · subst h0
        simp only [if_true]
        rw [if_neg (by omega)]
        have := colN_nonneg u hu' 0
        simpa using this
      · rw [if_neg h0, if_neg (by omega)]
        have := ih hu' (s - 1) (by omega) (by omega)
        simpa using this

/-- Monotonicity of the north columns of a word in `i` and `-1`: the column does not increase along the north steps. -/
theorem mon_i_neg (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) :
    ∀ s : ℤ, 0 ≤ s → s + 1 < cntI u → colN u (0, 0) (s + 1) ≤ colN u (0, 0) s := by
  induction u with
  | nil => intro s _ h; simp [cntI] at h; omega
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    intro s hs0 hs1
    rcases hx with rfl | rfl
    · have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at hs1
      rw [colN_cons_i, colN_cons_i]
      by_cases h0 : s = 0
      · subst h0
        simp only [if_true]
        rw [if_neg (by omega)]
        have := colN_nonpos u hu' 0
        simpa using this
      · rw [if_neg h0, if_neg (by omega)]
        have := ih hu' (s - 1) (by omega) (by omega)
        simpa using this
    · have hc : cntI (Unit4.negOne :: u) = cntI u := by simp [cntI]
      rw [hc] at hs1
      have e1 := colN_cons_negOne u (s + 1)
      have e2 := colN_cons_negOne u s
      rw [e1, e2]
      linarith [ih hu' s hs0 hs1]

/-- A palindrome of length at least two has the form `x :: (mid ++ [x])` with `mid` a palindrome. -/
theorem pal_decomp (x : Unit4) (rest : F2Word) (h : (x :: rest).reverse = x :: rest) (hr : rest ≠ []) :
    ∃ mid : F2Word, rest = mid ++ [x] ∧ mid.reverse = mid := by
  obtain ⟨mid, g, hg⟩ : ∃ mid g, rest = mid ++ [g] :=
    ⟨rest.dropLast, rest.getLast hr, (List.dropLast_append_getLast hr).symm⟩
  subst hg
  have h1 : (x :: (mid ++ [g])).reverse = (g :: mid.reverse) ++ [x] := by simp [List.reverse_append]
  rw [h1, List.cons_append] at h
  have hgx : g = x := (List.cons.inj h).1
  have htail := (List.cons.inj h).2
  rw [hgx] at htail
  exact ⟨mid, by rw [hgx], List.append_cancel_right htail⟩

theorem sum_cons' (x : Unit4) (u : F2Word) : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by
  simp [F2Word.sum]

theorem sum_append' (u v : F2Word) : F2Word.sum (u ++ v) = F2Word.sum u + F2Word.sum v := by
  simp [F2Word.sum]

theorem sum_nil' : F2Word.sum [] = 0 := by simp [F2Word.sum]

theorem colN_single_i (p : GInt) (b : ℤ) : colN [Unit4.i] p b = p.1 := by
  simp [colN, Unit4.vec]

/-- The palindrome identity: for a palindrome in the letters `1`, `i`, `-1`, the north columns of the `k`-th and the
`(cntI - 1 - k)`-th north steps sum to the first coordinate sum. -/
theorem pal_sum_aux (n : ℕ) : ∀ u : F2Word, u.length ≤ n → (∀ x ∈ u, x = .one ∨ x = .i ∨ x = .negOne) →
    u.reverse = u → ∀ s : ℤ, 0 ≤ s → s < cntI u →
    colN u (0, 0) s + colN u (0, 0) (cntI u - 1 - s) = (F2Word.sum u).1 := by
  induction n with
  | zero =>
    intro u hl _ _ s _ hs
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0
    simp [cntI] at hs
    omega
  | succ n ih =>
    intro u hl hu hp s hs0 hs
    cases u with
    | nil => simp [cntI] at hs; omega
    | cons x rest =>
      by_cases hr : rest = []
      · subst hr
        have hx := hu x (List.mem_cons_self ..)
        rcases hx with rfl | rfl | rfl
        · simp [cntI] at hs; omega
        · have h0 : s = 0 := by simp [cntI] at hs; omega
          subst h0
          simp [colN_cons_i, F2Word.sum, cntI, Unit4.vec]
        · simp [cntI] at hs; omega
      · obtain ⟨mid, hmid, hpm⟩ := pal_decomp x rest hp hr
        subst hmid
        have hlen : mid.length ≤ n := by simp at hl; omega
        have hmu : ∀ y ∈ mid, y = .one ∨ y = .i ∨ y = .negOne := fun y hy => hu y (by simp [hy])
        have hnn : ∀ y ∈ mid, y ≠ .negI := fun y hy => by
          rcases hmu y hy with h | h | h <;> simp [h]
        have hq := cntI_nonneg mid
        have hx : x = .one ∨ x = .i ∨ x = .negOne := hu x (List.mem_cons_self ..)
        rcases hx with rfl | rfl | rfl
        · have hc : cntI (Unit4.one :: (mid ++ [Unit4.one])) = cntI mid := by simp [cntI, cntI_append]
          rw [hc] at hs ⊢
          have hsum : (F2Word.sum (Unit4.one :: (mid ++ [Unit4.one]))).1 = (F2Word.sum mid).1 + 2 := by
            simp [sum_cons', sum_append', sum_nil', Unit4.vec]
            ring
          rw [colN_cons_one, colN_cons_one,
            colN_lo mid [Unit4.one] hnn (0, 0) s (by simpa using hs0) (by simpa using hs),
            colN_lo mid [Unit4.one] hnn (0, 0) (cntI mid - 1 - s) (by dsimp only; omega)
              (by dsimp only; omega), hsum]
          have ih' := ih mid hlen hmu hpm s hs0 (by omega)
          linarith
        · have hc : cntI (Unit4.i :: (mid ++ [Unit4.i])) = cntI mid + 2 := by
            simp [cntI, cntI_append]; ring
          rw [hc] at hs ⊢
          have hsumL : (F2Word.sum (Unit4.i :: (mid ++ [Unit4.i]))).1 = (F2Word.sum mid).1 := by
            simp [sum_cons', sum_append', sum_nil', Unit4.vec]
          have hlast : colN (mid ++ [Unit4.i]) (0, 0) (cntI mid) = (F2Word.sum mid).1 := by
            rw [colN_hi mid [Unit4.i] hnn (0, 0) (cntI mid) (by simp), colN_single_i]
            simp
          by_cases h0 : s = 0
          · subst h0
            rw [colN_cons_i _ 0, if_pos rfl, colN_cons_i _ (cntI mid + 2 - 1 - 0),
              if_neg (by omega), show cntI mid + 2 - 1 - 0 - 1 = cntI mid by ring, hlast, hsumL]
            ring
          · by_cases hN : s = cntI mid + 1
            · subst hN
              rw [show cntI mid + 2 - 1 - (cntI mid + 1) = 0 by ring, colN_cons_i _ 0, if_pos rfl,
                colN_cons_i _ (cntI mid + 1), if_neg (by omega), show cntI mid + 1 - 1 = cntI mid by ring,
                hlast, hsumL]
              ring
            · rw [colN_cons_i _ s, if_neg h0, colN_cons_i _ (cntI mid + 2 - 1 - s),
                if_neg (by omega)]
              have e1 : colN (mid ++ [Unit4.i]) (0, 0) (s - 1) = colN mid (0, 0) (s - 1) :=
                colN_lo mid [Unit4.i] hnn (0, 0) (s - 1) (by dsimp only; omega)
                  (by dsimp only; omega)
              have e2 : colN (mid ++ [Unit4.i]) (0, 0) (cntI mid + 2 - 1 - s - 1)
                  = colN mid (0, 0) (cntI mid - 1 - (s - 1)) := by
                rw [show cntI mid + 2 - 1 - s - 1 = cntI mid - 1 - (s - 1) by ring]
                exact colN_lo mid [Unit4.i] hnn (0, 0) _ (by dsimp only; omega)
                  (by dsimp only; omega)
              have ih' := ih mid hlen hmu hpm (s - 1) (by omega) (by omega)
              rw [e1, e2, hsumL]
              linarith
        · have hc : cntI (Unit4.negOne :: (mid ++ [Unit4.negOne])) = cntI mid := by simp [cntI, cntI_append]
          rw [hc] at hs ⊢
          have hsum : (F2Word.sum (Unit4.negOne :: (mid ++ [Unit4.negOne]))).1 = (F2Word.sum mid).1 - 2 := by
            simp [sum_cons', sum_append', sum_nil', Unit4.vec]
            ring
          rw [colN_cons_negOne, colN_cons_negOne,
            colN_lo mid [Unit4.negOne] hnn (0, 0) s (by simpa using hs0) (by simpa using hs),
            colN_lo mid [Unit4.negOne] hnn (0, 0) (cntI mid - 1 - s) (by dsimp only; omega)
              (by dsimp only; omega), hsum]
          have ih' := ih mid hlen hmu hpm s hs0 (by omega)
          linarith

end FLatticePaper.Tiles
