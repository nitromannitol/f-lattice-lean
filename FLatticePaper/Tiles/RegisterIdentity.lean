import FLatticePaper.Tiles.RegisterInduction
import FLatticePaper.Tiles.RegisterLink

/-! Task Q25 (c), the register identification.

The registers after a word are the bottom edges of its sources: the odd register after `u` is the odd bottom edge of the
prefix before the last letter `1` or `2`, and the even register after `u` is the even bottom edge of the prefix before the
last letter `1` or `3` (`regsAfter_fst`, `regsAfter_snd`). By the register link these are the pseudo-square maps of the
ceiling parent words (`regsAfter_fst_gH`, `regsAfter_snd_gH`). -/

namespace FLatticePaper.Tiles.RegisterIdentity

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.RecursionIdentity
  FLatticePaper.Tiles.RegisterInduction FLatticePaper.Tiles.RegisterLink

theorem regsGo_eq_regsFrom (w : Word) : ∀ (pre : Word) (regs : F2Word × F2Word),
    regsGo pre w regs = regsFrom pre w regs := by
  induction w with
  | nil => intro pre regs; rfl
  | cons x rest ih => intro pre regs; simp only [regsGo, regsFrom, ih]

theorem regsAfter_eq_regsFrom (w : Word) : regsAfter w = regsFrom [] w ([], []) :=
  regsGo_eq_regsFrom w [] ([], [])

/-- The registers after a snoc: the update by the last letter, at the bottom edges of the prefix. -/
theorem regsAfter_snoc (v : Word) (x : Digit) :
    regsAfter (v ++ [x]) = updateRegs x (regsAfter v) (bottomEdges v) := by
  have h := regsFrom_snoc x [] v ([], [])
  rw [regsAfter_eq_regsFrom, h, ← regsAfter_eq_regsFrom, List.nil_append, ← bottomEdges_eq_regs]

/-- The odd register after `u` is the odd bottom edge of the odd source of `u`. -/
theorem regsAfter_fst (u : Word) (h : ∃ y ∈ u, y = Digit.one ∨ y = Digit.two) :
    (regsAfter u).1 = (bottomEdges (srcOf u).1).1 := by
  induction u using List.reverseRecOn with
  | nil => exact absurd h (by simp)
  | append_singleton v x ih =>
    rw [regsAfter_snoc, srcOf_fst_snoc]
    cases x with
    | one => simp [updateRegs]
    | two => simp [updateRegs]
    | three =>
      have h' : ∃ y ∈ v, y = Digit.one ∨ y = Digit.two := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.1 hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      simp only [updateRegs, if_neg (show ¬(Digit.three = Digit.one ∨ Digit.three = Digit.two) by decide)]
      exact ih h'

/-- The even register after `u` is the even bottom edge of the even source of `u`. -/
theorem regsAfter_snd (u : Word) (h : ∃ y ∈ u, y = Digit.one ∨ y = Digit.three) :
    (regsAfter u).2 = (bottomEdges (srcOf u).2).2 := by
  induction u using List.reverseRecOn with
  | nil => exact absurd h (by simp)
  | append_singleton v x ih =>
    rw [regsAfter_snoc, srcOf_snd_snoc]
    cases x with
    | one => simp [updateRegs]
    | three => simp [updateRegs]
    | two =>
      have h' : ∃ y ∈ v, y = Digit.one ∨ y = Digit.three := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.1 hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      simp only [updateRegs, if_neg (show ¬(Digit.two = Digit.one ∨ Digit.two = Digit.three) by decide)]
      exact ih h'

/-- **The odd register is the ceiling pair word of the odd parent (Q25 (c)).** -/
theorem regsAfter_fst_gH (u : Word) (h : ∃ y ∈ u, y = Digit.one ∨ y = Digit.two) :
    (regsAfter u).1 = gH (quadAt [] u).parentP := by
  rw [regsAfter_fst u h, parentP_eq_childP_srcOf u h, oddBottom_eq_gH]

/-- **The even register is the ceiling pair word of the even parent (Q25 (c)).** -/
theorem regsAfter_snd_gH (u : Word) (h : ∃ y ∈ u, y = Digit.one ∨ y = Digit.three) :
    (regsAfter u).2 = gH (quadAt [] u).parentQ := by
  rw [regsAfter_snd u h, parentQ_eq_childQ_srcOf u h, evenBottom_eq_gH]

end FLatticePaper.Tiles.RegisterIdentity
