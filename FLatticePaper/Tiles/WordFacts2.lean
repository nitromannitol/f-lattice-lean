import FLatticePaper.Tiles.WordFacts1
import FLatticePaper.Tiles.CoveringRows

/-! Column facts of words in `i` and `-1` (the words `w2`, rotated by `-i` to `w2' = w2.map mulNegI` in `1` and `i`):
the lower bound `X_2 ≤ c_s`, and the gap bound `c_s - 1 ≤ c_{s+2}` when every `-1` is followed by two `i`s. -/

namespace FLatticePaper.Tiles

/-- Every `-1` of the word is followed by `k` letters `i`. -/
def NFollowedBy (k : ℕ) (u : F2Word) : Prop :=
  ∀ j : ℕ, u[j]? = some .negOne → ∀ m : ℕ, m < k → u[j + 1 + m]? = some .i

theorem nf_tail {k : ℕ} {x : Unit4} {v : F2Word} (h : NFollowedBy k (x :: v)) : NFollowedBy k v := by
  intro j hj m hm
  have := h (j + 1) (by simpa using hj) m hm
  rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega] at this
  simpa using this

/-- The first north column is at least the first coordinate sum of the word in `i` and `-1`. -/
theorem sum_fst_le_colN_neg : ∀ u : F2Word, (∀ x ∈ u, x = .i ∨ x = .negOne) →
    ∀ s : ℤ, 0 ≤ s → s < cntI u → (F2Word.sum u).1 ≤ colN u (0, 0) s := by
  intro u
  induction u with
  | nil => intro _ s _ h; simp [cntI] at h; omega
  | cons x v ih =>
    intro hu s hs hlt
    have hv : ∀ y ∈ v, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    rcases hu x List.mem_cons_self with rfl | rfl
    · rw [sum_cons', colN_cons_i]
      have e : (Unit4.vec Unit4.i + F2Word.sum v).1 = (F2Word.sum v).1 := by simp [Unit4.vec]
      rw [e]
      by_cases hs0 : s = 0
      · subst hs0
        simp only [if_true]
        exact sum_fst_nonpos v hv
      · rw [if_neg hs0]
        exact ih hv (s - 1) (by omega) (by simp [cntI] at hlt; omega)
    · rw [sum_cons', colN_cons_negOne]
      have e : (Unit4.vec Unit4.negOne + F2Word.sum v).1 = -1 + (F2Word.sum v).1 := by simp [Unit4.vec]
      rw [e]
      have := ih hv s hs (by simp [cntI] at hlt; omega)
      linarith

/-- The column of the first `i` of a word where every `-1` is followed by two `i`s is at least `-1`. -/
theorem nf_colN_zero {v : F2Word} (hv : ∀ x ∈ v, x = .i ∨ x = .negOne) (hN : NFollowedBy 2 v)
    (h1 : 1 ≤ cntI v) : -1 ≤ colN v (0, 0) 0 := by
  cases v with
  | nil => simp [cntI] at h1
  | cons x v1 =>
    rcases hv x List.mem_cons_self with rfl | rfl
    · rw [colN_cons_i]; simp
    · have h0 := hN 0 (by simp) 0 (by norm_num)
      have h1' := hN 0 (by simp) 1 (by norm_num)
      cases v1 with
      | nil => simp at h0
      | cons y v2 =>
        have hy : y = .i := by simpa using h0
        subst hy
        rw [colN_cons_negOne, colN_cons_i]
        simp

/-- As `nf_colN_zero`, for the second north column. -/
theorem nf_colN_one {v : F2Word} (hv : ∀ x ∈ v, x = .i ∨ x = .negOne) (hN : NFollowedBy 2 v)
    (h2 : 2 ≤ cntI v) : -1 ≤ colN v (0, 0) 1 := by
  cases v with
  | nil => simp [cntI] at h2
  | cons x v1 =>
    rcases hv x List.mem_cons_self with rfl | rfl
    · rw [colN_cons_i, if_neg (by norm_num)]
      have hv1 : ∀ y ∈ v1, y = .i ∨ y = .negOne := fun y hy => hv y (List.mem_cons_of_mem _ hy)
      have := nf_colN_zero hv1 (nf_tail hN) (by simp [cntI] at h2; omega)
      norm_num
      exact this
    · have h0 := hN 0 (by simp) 0 (by norm_num)
      have h1' := hN 0 (by simp) 1 (by norm_num)
      cases v1 with
      | nil => simp at h0
      | cons y v2 =>
        have hy : y = .i := by simpa using h0
        subst hy
        cases v2 with
        | nil => simp at h1'
        | cons z v3 =>
          have hz : z = .i := by simpa using h1'
          subst hz
          simp [colN_cons_negOne, colN_cons_i]

/-- The gap bound: when every `-1` is followed by two `i`s, the north columns satisfy `c_s - 1 ≤ c_{s+2}`. -/
theorem gapN2 : ∀ u : F2Word, (∀ x ∈ u, x = .i ∨ x = .negOne) → NFollowedBy 2 u →
    ∀ s : ℤ, 0 ≤ s → s + 2 < cntI u → colN u (0, 0) s - 1 ≤ colN u (0, 0) (s + 2) := by
  intro u
  induction u with
  | nil => intro _ _ s _ h; simp [cntI] at h; omega
  | cons x v ih =>
    intro hu hN s hs hlt
    have hv : ∀ y ∈ v, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hNv := nf_tail hN
    rcases hu x List.mem_cons_self with rfl | rfl
    · rw [colN_cons_i, colN_cons_i, if_neg (show s + 2 ≠ 0 by omega)]
      have hlt' : s + 2 < 1 + cntI v := by simpa [cntI] using hlt
      by_cases hs0 : s = 0
      · subst hs0
        have := nf_colN_one hv hNv (by omega)
        simp only [if_true]
        norm_num
        simpa using this
      · rw [if_neg hs0]
        have := ih hv hNv (s - 1) (by omega) (by omega)
        rw [show s - 1 + 2 = s - 1 + 2 from rfl] at this
        rw [show s + 2 - 1 = s - 1 + 2 by ring]
        linarith
    · rw [colN_cons_negOne, colN_cons_negOne]
      have hlt' : s + 2 < cntI v := by simpa [cntI] using hlt
      have := ih hv hNv s hs hlt'
      linarith

end FLatticePaper.Tiles
