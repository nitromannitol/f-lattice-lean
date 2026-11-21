import FLatticePaper.Tiles.RowAdmiss

/-! Column facts of admissible words in `1` and `i`, for the successor condition: a run of ones after each `i` gives a
gap between consecutive north columns, and the palindrome and the two decompositions (case b, case c) give the sums
`n_t + n_{q-t}` used at the bottom right ends. -/

namespace FLatticePaper.Tiles

/-- A word whose first `k` letters are `1` has north column at least `k` at the first `i`. -/
theorem ones_le_colN (k : ℕ) : ∀ v : F2Word, (∀ x ∈ v, x = .one ∨ x = .i) →
    (∀ m : ℕ, m < k → v[m]? = some .one) → 0 < cntI v → (k : ℤ) ≤ colN v (0, 0) 0 := by
  induction k with
  | zero => intro v hv _ _; simpa using colN_nonneg v hv 0
  | succ k ih =>
    intro v hv hk hpos
    cases v with
    | nil => simp [cntI] at hpos
    | cons x v' =>
      have hx : x = .one := by
        have := hk 0 (Nat.succ_pos k)
        simpa using this
      subst hx
      have hk' : ∀ m : ℕ, m < k → v'[m]? = some .one := fun m hm => by
        have := hk (m + 1) (by omega)
        simpa using this
      have hv' : ∀ y ∈ v', y = .one ∨ y = .i := fun y hy => hv y (List.mem_cons_of_mem _ hy)
      have hpos' : 0 < cntI v' := by simpa [cntI] using hpos
      have := ih v' hv' hk' hpos'
      rw [colN_cons_one]
      push_cast
      linarith

/-- Consecutive north columns of a word in `1` and `i` in which every `i` is followed by `k` ones differ by at least
`k`. -/
theorem colN_gap (k : ℕ) : ∀ u : F2Word, (∀ x ∈ u, x = .one ∨ x = .i) →
    (∀ j : ℕ, u[j]? = some .i → ∀ m : ℕ, m < k → u[j + 1 + m]? = some .one) →
    ∀ s : ℤ, 0 ≤ s → s + 1 < cntI u → colN u (0, 0) s + k ≤ colN u (0, 0) (s + 1) := by
  intro u
  induction u with
  | nil => intro _ _ s _ h; simp [cntI] at h; omega
  | cons x v ih =>
    intro hu hk s hs hlt
    have hv : ∀ y ∈ v, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rcases hu x List.mem_cons_self with hx | hx
    · subst hx
      have hk' : ∀ j : ℕ, v[j]? = some .i → ∀ m : ℕ, m < k → v[j + 1 + m]? = some .one := by
        intro j hj m hm
        have h := hk (j + 1) (by simpa using hj) m hm
        rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega] at h
        simpa using h
      have hlt' : s + 1 < cntI v := by simpa [cntI] using hlt
      rw [colN_cons_one, colN_cons_one]
      have := ih hv hk' s hs hlt'
      linarith
    · subst hx
      have hcnt : cntI (Unit4.i :: v) = 1 + cntI v := by simp [cntI]
      have hk' : ∀ j : ℕ, v[j]? = some .i → ∀ m : ℕ, m < k → v[j + 1 + m]? = some .one := by
        intro j hj m hm
        have h := hk (j + 1) (by simpa using hj) m hm
        rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega] at h
        simpa using h
      rw [hcnt] at hlt
      by_cases hs0 : s = 0
      · subst hs0
        have hones : ∀ m : ℕ, m < k → v[m]? = some .one := fun m hm => by
          have h := hk 0 (by simp) m hm
          rw [show (0 : ℕ) + 1 + m = m + 1 by omega] at h
          simpa using h
        have hk0 := ones_le_colN k v hv hones (by omega)
        rw [colN_cons_i, colN_cons_i]
        norm_num
        linarith
      · have hs1 : 1 ≤ s := by omega
        rw [colN_cons_i, colN_cons_i, if_neg hs0, if_neg (show s + 1 ≠ 0 by omega)]
        have hlt' : s - 1 + 1 < cntI v := by omega
        have := ih hv hk' (s - 1) (by omega) hlt'
        rw [show s - 1 + 1 = s by ring, show s + 1 - 1 = s by ring] at *
        linarith

/-- The first letter of an admissible word is `1`, so its first north column is at least one when it has an `i`. -/
theorem adm_head_colN {w : F2Word} (hA : Admissible w) (hq : 0 < cntI w) : 1 ≤ colN w (0, 0) 0 := by
  have hmono : ∀ x ∈ w, x = .one ∨ x = .i := hA.1
  obtain ⟨-, hhead, -, -⟩ := hA
  cases w with
  | nil => simp at hhead
  | cons x v =>
    have hx : x = .one := by simpa using hhead
    subst hx
    rw [colN_cons_one]
    have := colN_nonneg v (fun y hy => hmono y (List.mem_cons_of_mem _ hy)) 0
    linarith

/-- The last letter of an admissible word is `1`, so the last north column is at most `P - 1`. -/
theorem adm_last_colN {w : F2Word} (hA : Admissible w) {s : ℤ} (hs0 : 0 ≤ s) (hs : s < cntI w) :
    colN w (0, 0) s ≤ (F2Word.sum w).1 - 1 := by
  obtain ⟨hmono, -, hlast, -⟩ := hA
  obtain ⟨u, rfl⟩ : ∃ u, w = u ++ [.one] := by
    rcases List.eq_nil_or_concat w with h | ⟨L, b, h⟩
    · subst h; simp at hlast
    · subst h
      have hb : b = .one := by simpa using hlast
      exact ⟨L, by rw [hb, List.concat_eq_append]⟩
  have hu : ∀ x ∈ u, x ≠ .negI := fun x hx => by
    rcases hmono x (List.mem_append_left _ hx) with h | h <;> simp [h]
  have hcnt : cntI (u ++ [.one]) = cntI u := by simp [cntI_append, cntI]
  rw [hcnt] at hs
  rw [colN_lo u [.one] hu (0, 0) s (by simp; exact hs0) (by simpa using hs)]
  have hle := colN_le_sum u (fun x hx => hmono x (List.mem_append_left _ hx)) s
  have hsum : (F2Word.sum (u ++ [.one])).1 = (F2Word.sum u).1 + 1 := by
    rw [sum_append']
    simp [F2Word.sum, Unit4.vec]
  rw [hsum]
  linarith

/-- The palindrome identity of an admissible palindrome in `1` and `i`. -/
theorem adm_pal_sum {w : F2Word} (hmono : Monotone w) (hpal : w.reverse = w) {s : ℤ} (hs0 : 0 ≤ s)
    (hs : s < cntI w) : colN w (0, 0) s + colN w (0, 0) (cntI w - 1 - s) = (F2Word.sum w).1 := by
  have hlet3 : ∀ x ∈ w, x = .one ∨ x = .i ∨ x = .negOne := fun x hx =>
    (hmono x hx).elim Or.inl (fun h => Or.inr (Or.inl h))
  exact pal_sum_aux w.length w le_rfl hlet3 hpal s hs0 hs

/-- The strict rise of north columns of a non-palindromic admissible word: consecutive `i`s are separated by a `1`
(case b) or by three `1`s (case c). -/
theorem adm_strict {w : F2Word} (hA : Admissible w) (hnp : w.reverse ≠ w) {t : ℤ} (ht0 : 0 ≤ t)
    (ht1 : t + 1 < cntI w) : colN w (0, 0) t + 1 ≤ colN w (0, 0) (t + 1) := by
  obtain ⟨hmono, -, -, hcase⟩ := hA
  have hlet : ∀ x ∈ w, x = .one ∨ x = .i := hmono
  rcases hcase with hpal | ⟨wt, -, -, hifol⟩ | ⟨wt, -, -, hifol⟩
  · exact absurd hpal hnp
  · have := colN_gap 1 w hlet hifol t ht0 ht1
    push_cast at this
    linarith
  · have := colN_gap 3 w hlet hifol t ht0 ht1
    push_cast at this
    linarith

/-- The bound at the bottom right ends below the south steps of the first admissible class:
`P ≤ n_t + n_{q-t}` for `1 ≤ t ≤ q - 1`. -/
theorem adm_A2 {w : F2Word} (hA : Admissible w) {t : ℤ} (ht1 : 1 ≤ t) (ht2 : t ≤ cntI w - 1) :
    (F2Word.sum w).1 ≤ colN w (0, 0) t + colN w (0, 0) (cntI w - t) := by
  have hmono : ∀ x ∈ w, x = .one ∨ x = .i := hA.1
  have hcase := hA.2.2.2
  rcases hcase with hpal | ⟨wt, hw, hwt, hifol⟩ | ⟨wt, hw, hwt, hifol⟩
  · have hid := adm_pal_sum hmono hpal (s := t) (by omega) (by omega)
    have hmon := mon_one_i w hmono (cntI w - 1 - t) (by omega) (by omega)
    have e : cntI w - 1 - t + 1 = cntI w - t := by ring
    rw [e] at hmon
    linarith
  · have e1 : w = Unit4.one :: Unit4.one :: Unit4.i :: (wt ++ [Unit4.one]) := by rw [hw]; simp
    subst e1
    have hwlet : ∀ x ∈ wt, x = .one ∨ x = .i := fun x hx => hmono x (by simp [hx])
    have hwnI : ∀ x ∈ wt, x ≠ .negI := fun x hx => by rcases hwlet x hx with h | h <;> simp [h]
    have hwmono : Monotone wt := fun x hx => hwlet x hx
    rw [cntI_b] at ht2 ⊢
    rw [sum_fst_b, colN_b, colN_b, if_neg (show t ≠ 0 by omega), if_neg (show cntI wt + 1 - t ≠ 0 by omega)]
    have h1 : colN (wt ++ [Unit4.one]) (0, 0) (t - 1) = colN wt (0, 0) (t - 1) :=
      colN_lo wt [Unit4.one] hwnI (0, 0) (t - 1) (by simp; omega) (by simp; omega)
    have h2 : colN (wt ++ [Unit4.one]) (0, 0) (cntI wt + 1 - t - 1) = colN wt (0, 0) (cntI wt + 1 - t - 1) :=
      colN_lo wt [Unit4.one] hwnI (0, 0) _ (by simp; omega) (by simp; omega)
    have hid := adm_pal_sum hwmono hwt (s := t - 1) (by omega) (by omega)
    have e2 : cntI wt - 1 - (t - 1) = cntI wt + 1 - t - 1 := by ring
    rw [e2] at hid
    rw [h1, h2]
    linarith
  · have e1 : w = Unit4.one :: (wt ++ [Unit4.one, Unit4.one, Unit4.one]) := by rw [hw]; simp
    subst e1
    have hwlet : ∀ x ∈ wt, x = .one ∨ x = .i := fun x hx => hmono x (by simp [hx])
    have hwnI : ∀ x ∈ wt, x ≠ .negI := fun x hx => by rcases hwlet x hx with h | h <;> simp [h]
    have hwmono : Monotone wt := fun x hx => hwlet x hx
    rw [cntI_c] at ht2 ⊢
    rw [sum_fst_c, colN_c, colN_c]
    have h1 : colN (wt ++ [Unit4.one, Unit4.one, Unit4.one]) (0, 0) t = colN wt (0, 0) t :=
      colN_lo wt [Unit4.one, Unit4.one, Unit4.one] hwnI (0, 0) t (by simp; omega) (by simp; omega)
    have h2 : colN (wt ++ [Unit4.one, Unit4.one, Unit4.one]) (0, 0) (cntI wt - t)
        = colN wt (0, 0) (cntI wt - t) :=
      colN_lo wt [Unit4.one, Unit4.one, Unit4.one] hwnI (0, 0) _ (by simp; omega) (by simp; omega)
    rw [h1, h2]
    have hid := adm_pal_sum hwmono hwt (s := t) (by omega) (by omega)
    have hg := colN_gap 3 (Unit4.one :: (wt ++ [Unit4.one, Unit4.one, Unit4.one])) hmono hifol
      (cntI wt - 1 - t) (by omega) (by rw [cntI_c]; omega)
    rw [colN_c, colN_c] at hg
    have e3 : cntI wt - 1 - t + 1 = cntI wt - t := by ring
    rw [e3] at hg
    push_cast at hg
    have hg' : colN (wt ++ [Unit4.one, Unit4.one, Unit4.one]) (0, 0) (cntI wt - 1 - t) + 3
        ≤ colN (wt ++ [Unit4.one, Unit4.one, Unit4.one]) (0, 0) (cntI wt - t) := by linarith
    have hl1 : colN (wt ++ [Unit4.one, Unit4.one, Unit4.one]) (0, 0) (cntI wt - 1 - t)
        = colN wt (0, 0) (cntI wt - 1 - t) :=
      colN_lo wt [Unit4.one, Unit4.one, Unit4.one] hwnI (0, 0) _ (by simp; omega) (by simp; omega)
    rw [hl1, h2] at hg'
    have hid' := hid
    linarith

end FLatticePaper.Tiles
