import FLatticePaper.Tiles.RowInterval
import Mathlib.Tactic.Linarith

/-! Columns of the walks of a tile: translation to the origin, splitting at the two parts of the walk, the reflection of
south columns into north columns, and bounds for words in `{1, i}` and `{i, -1}`. -/

namespace FLatticePaper.Tiles

/-- Columns are translation-invariant: a walk from `p` is the walk from the origin shifted by `p`. -/
theorem colN_trans (u : F2Word) (p : GInt) (b : ℤ) :
    colN u p b = p.1 + colN u (0, 0) (b - p.2) := by
  induction u generalizing p b with
  | nil => simp [colN]
  | cons x u ih =>
    have e1 := ih (p + x.vec) b
    have e2 := ih ((0, 0) + x.vec) (b - p.2)
    simp only [colN]
    rw [e1, e2]
    by_cases hc : x = .i ∧ p.2 = b
    · have hc2 : x = .i ∧ (0 : ℤ) = b - p.2 := ⟨hc.1, by omega⟩
      rw [if_pos hc, if_pos hc2]
      simp
    · have hc2 : ¬ (x = .i ∧ (0 : ℤ) = b - p.2) := fun h => hc ⟨h.1, by omega⟩
      rw [if_neg hc, if_neg hc2]
      simp only [Prod.fst_add, Prod.snd_add]
      ring_nf

theorem colS_trans (u : F2Word) (p : GInt) (b : ℤ) :
    colS u p b = p.1 + colS u (0, 0) (b - p.2) := by
  induction u generalizing p b with
  | nil => simp [colS]
  | cons x u ih =>
    have e1 := ih (p + x.vec) b
    have e2 := ih ((0, 0) + x.vec) (b - p.2)
    simp only [colS]
    rw [e1, e2]
    by_cases hc : x = .negI ∧ p.2 = b + 1
    · have hc2 : x = .negI ∧ (0 : ℤ) = b - p.2 + 1 := ⟨hc.1, by omega⟩
      rw [if_pos hc, if_pos hc2]
      simp
    · have hc2 : ¬ (x = .negI ∧ (0 : ℤ) = b - p.2 + 1) := fun h => hc ⟨h.1, by omega⟩
      rw [if_neg hc, if_neg hc2]
      simp only [Prod.fst_add, Prod.snd_add]
      ring_nf

/-- Above the north steps of the first part (which contains no south step), the columns are those of the second part,
from the end point of the first part. -/
theorem colN_hi (u v : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) :
    ∀ (p : GInt) (b : ℤ), p.2 + cntI u ≤ b → colN (u ++ v) p b = colN v (p + F2Word.sum u) b := by
  induction u with
  | nil => intro p b _; simp [F2Word.sum]
  | cons x u ih =>
    intro p b hb
    have hx : x ≠ .negI := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    have hn := cntI_nonneg u
    cases x with
    | negI => exact absurd rfl hx
    | one =>
      have hc : cntI (Unit4.one :: u) = cntI u := by simp [cntI]
      rw [hc] at hb
      simp only [List.cons_append, colN]
      rw [if_neg (by simp), ih hu' (p + Unit4.vec .one) b (by simp [Unit4.vec]; omega), hs, ← add_assoc]
    | negOne =>
      have hc : cntI (Unit4.negOne :: u) = cntI u := by simp [cntI]
      rw [hc] at hb
      simp only [List.cons_append, colN]
      rw [if_neg (by simp), ih hu' (p + Unit4.vec .negOne) b (by simp [Unit4.vec]; omega), hs, ← add_assoc]
    | i =>
      have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at hb
      simp only [List.cons_append, colN]
      rw [if_neg (fun h => by have := h.2; simp [Unit4.vec] at *; omega)]
      rw [ih hu' (p + Unit4.vec .i) b (by simp [Unit4.vec]; omega), hs, ← add_assoc]

/-- Below the north steps of the end of the first part, the columns are those of the first part. -/
theorem colN_lo (u v : F2Word) (hu : ∀ x ∈ u, x ≠ .negI) :
    ∀ (p : GInt) (b : ℤ), p.2 ≤ b → b < p.2 + cntI u → colN (u ++ v) p b = colN u p b := by
  induction u with
  | nil => intro p b h1 h2; simp [cntI] at h2; omega
  | cons x u ih =>
    intro p b h1 h2
    have hx : x ≠ .negI := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .negI := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hn := cntI_nonneg u
    cases x with
    | negI => exact absurd rfl hx
    | one =>
      have hc : cntI (Unit4.one :: u) = cntI u := by simp [cntI]
      rw [hc] at h2
      simp only [List.cons_append, colN]
      rw [if_neg (by simp), if_neg (by simp), ih hu' (p + Unit4.vec .one) b (by simp [Unit4.vec]; omega)
        (by simp [Unit4.vec]; omega)]
    | negOne =>
      have hc : cntI (Unit4.negOne :: u) = cntI u := by simp [cntI]
      rw [hc] at h2
      simp only [List.cons_append, colN]
      rw [if_neg (by simp), if_neg (by simp), ih hu' (p + Unit4.vec .negOne) b (by simp [Unit4.vec]; omega)
        (by simp [Unit4.vec]; omega)]
    | i =>
      have hc : cntI (Unit4.i :: u) = 1 + cntI u := by simp [cntI]
      rw [hc] at h2
      simp only [List.cons_append, colN]
      by_cases hpb : p.2 = b
      · simp [hpb]
      · rw [if_neg (fun h => hpb h.2), if_neg (fun h => hpb h.2),
          ih hu' (p + Unit4.vec .i) b (by simp [Unit4.vec]; omega) (by simp [Unit4.vec]; omega)]

/-- Above the south steps of the first part (which contains no north step), the south columns are those of the second
part. -/
theorem colS_hi (u v : F2Word) (hu : ∀ x ∈ u, x ≠ .i) :
    ∀ (p : GInt) (b : ℤ), b + 1 ≤ p.2 - cntNegI u → colS (u ++ v) p b = colS v (p + F2Word.sum u) b := by
  induction u with
  | nil => intro p b _; simp [F2Word.sum]
  | cons x u ih =>
    intro p b hb
    have hx : x ≠ .i := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    have hn := cntNegI_nonneg u
    cases x with
    | i => exact absurd rfl hx
    | one =>
      have hc : cntNegI (Unit4.one :: u) = cntNegI u := by simp [cntNegI]
      rw [hc] at hb
      simp only [List.cons_append, colS]
      rw [if_neg (by simp), ih hu' (p + Unit4.vec .one) b (by simp [Unit4.vec]; omega), hs, ← add_assoc]
    | negOne =>
      have hc : cntNegI (Unit4.negOne :: u) = cntNegI u := by simp [cntNegI]
      rw [hc] at hb
      simp only [List.cons_append, colS]
      rw [if_neg (by simp), ih hu' (p + Unit4.vec .negOne) b (by simp [Unit4.vec]; omega), hs, ← add_assoc]
    | negI =>
      have hc : cntNegI (Unit4.negI :: u) = 1 + cntNegI u := by simp [cntNegI]
      rw [hc] at hb
      simp only [List.cons_append, colS]
      rw [if_neg (fun h => by have := h.2; simp [Unit4.vec] at *; omega)]
      rw [ih hu' (p + Unit4.vec .negI) b (by simp [Unit4.vec]; omega), hs, ← add_assoc]

/-- Within the south steps of the first part, the south columns are those of the first part. -/
theorem colS_lo (u v : F2Word) (hu : ∀ x ∈ u, x ≠ .i) :
    ∀ (p : GInt) (b : ℤ), p.2 - cntNegI u ≤ b → b + 1 ≤ p.2 → colS (u ++ v) p b = colS u p b := by
  induction u with
  | nil => intro p b h1 h2; simp [cntNegI] at h1; omega
  | cons x u ih =>
    intro p b h1 h2
    have hx : x ≠ .i := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y ≠ .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hn := cntNegI_nonneg u
    cases x with
    | i => exact absurd rfl hx
    | one =>
      have hc : cntNegI (Unit4.one :: u) = cntNegI u := by simp [cntNegI]
      rw [hc] at h1
      simp only [List.cons_append, colS]
      rw [if_neg (by simp), if_neg (by simp), ih hu' (p + Unit4.vec .one) b (by simp [Unit4.vec]; omega)
        (by simp [Unit4.vec]; omega)]
    | negOne =>
      have hc : cntNegI (Unit4.negOne :: u) = cntNegI u := by simp [cntNegI]
      rw [hc] at h1
      simp only [List.cons_append, colS]
      rw [if_neg (by simp), if_neg (by simp), ih hu' (p + Unit4.vec .negOne) b (by simp [Unit4.vec]; omega)
        (by simp [Unit4.vec]; omega)]
    | negI =>
      have hc : cntNegI (Unit4.negI :: u) = 1 + cntNegI u := by simp [cntNegI]
      rw [hc] at h1
      simp only [List.cons_append, colS]
      by_cases hpb : p.2 = b + 1
      · simp [hpb]
      · rw [if_neg (fun h => hpb h.2), if_neg (fun h => hpb h.2),
          ih hu' (p + Unit4.vec .negI) b (by simp [Unit4.vec]; omega) (by simp [Unit4.vec]; omega)]

/-- The reflection of a word: its south columns are the negated north columns of the word. -/
theorem colS_map_neg (u : F2Word) (h : ℤ) :
    colS (u.map Unit4.neg) (0, 0) h = -colN u (0, 0) (-h - 1) := by
  induction u generalizing h with
  | nil => simp [colS, colN]
  | cons x u ih =>
    have e1 := colS_trans (u.map Unit4.neg) ((0, 0) + (Unit4.neg x).vec) h
    have e2 := colN_trans u ((0, 0) + x.vec) (-h - 1)
    have e3 := ih (h - ((0, 0) + (Unit4.neg x).vec).2)
    simp only [List.map_cons, colS, colN]
    rw [e1, e3, e2]
    cases x
    all_goals (try simp [Unit4.neg, Unit4.vec])
    all_goals (try ring_nf)
    all_goals (try omega)

/-- The first coordinate sum of a word with letters `1` and `i` is nonnegative. -/
theorem sum_fst_nonneg (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) : 0 ≤ (F2Word.sum u).1 := by
  induction u with
  | nil => simp [F2Word.sum]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    rw [hs, Prod.fst_add]
    rcases hx with rfl | rfl <;> simp [Unit4.vec] <;> linarith [ih hu']

/-- A north column of a word with letters `1` and `i` is at most its first coordinate sum. -/
theorem colN_le_sum (u : F2Word) (hu : ∀ x ∈ u, x = .one ∨ x = .i) (s : ℤ) :
    colN u (0, 0) s ≤ (F2Word.sum u).1 := by
  induction u generalizing s with
  | nil => simp [colN, F2Word.sum]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .one ∨ y = .i := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have hnn := sum_fst_nonneg u hu'
    have hs : F2Word.sum (x :: u) = x.vec + F2Word.sum u := by simp [F2Word.sum]
    have e := colN_trans u ((0, 0) + Unit4.vec x) s
    have ih' := ih hu' (s - (Unit4.vec x).2)
    simp only [colN]
    rw [hs, Prod.fst_add]
    by_cases hc : x = .i ∧ (0 : ℤ) = s
    · rw [if_pos (by simpa using hc)]
      rcases hx with rfl | rfl
      all_goals (try simp [Unit4.vec] at *)
      all_goals (try omega)
    · rw [if_neg (by simpa using hc), e]
      simp only [Prod.fst_add, Prod.snd_add, zero_add] at *
      linarith

/-- A north column of a word with letters `i` and `-1` is at most zero. -/
theorem colN_nonpos (u : F2Word) (hu : ∀ x ∈ u, x = .i ∨ x = .negOne) (s : ℤ) :
    colN u (0, 0) s ≤ 0 := by
  induction u generalizing s with
  | nil => simp [colN]
  | cons x u ih =>
    have hx := hu x (List.mem_cons_self ..)
    have hu' : ∀ y ∈ u, y = .i ∨ y = .negOne := fun y hy => hu y (List.mem_cons_of_mem _ hy)
    have e := colN_trans u ((0, 0) + Unit4.vec x) s
    have ih' := ih hu' (s - (Unit4.vec x).2)
    simp only [colN]
    by_cases hc : x = .i ∧ (0 : ℤ) = s
    · rw [if_pos (by simpa using hc)]
    · rw [if_neg (by simpa using hc), e]
      simp only [Prod.fst_add, Prod.snd_add, zero_add] at *
      rcases hx with rfl | rfl <;> simp [Unit4.vec] at * <;> linarith

end FLatticePaper.Tiles
