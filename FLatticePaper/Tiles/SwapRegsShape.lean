import FLatticePaper.Tiles.WeakStepPaper

/-! # The shape of a word from its register pair

The first register `(regsAt w).1` is set by the letters `one` and `two` (to the prefix before the letter) and left alone by
`three`; the second register is set by `one` and `three` and left alone by `two`. Hence the register words of a word are read
off from its last non-trailing letter: `w = u1 · d · 3^m` with `d ∈ {1,2}`, and `w = u2 · d' · 2^m` with `d' ∈ {1,3}`. -/

namespace FLatticePaper.Tiles.SwapRegsShape

open FLatticePaper.Farey
open FLatticePaper.Tiles.SurgicalWeak

/-- The first register of `w` is `u1`: `w` is `u1` followed by a letter `one` or `two`, then `m` letters `three`. -/
theorem regsAt_fst_shape (w u1 : Word) (h : (regsAt w).1 = some u1) :
    ∃ (d : Digit) (m : ℕ), (d = Digit.one ∨ d = Digit.two) ∧ w = u1 ++ [d] ++ List.replicate m Digit.three := by
  induction w using List.reverseRecOn generalizing u1 with
  | nil => simp [regsAt, regRun] at h
  | append_singleton v x ih =>
    rw [WeakStepPaper.regsAt_snoc] at h
    cases x with
    | one =>
      refine ⟨Digit.one, 0, Or.inl rfl, ?_⟩
      simp only [regStep] at h
      cases h
      simp
    | two =>
      refine ⟨Digit.two, 0, Or.inr rfl, ?_⟩
      simp only [regStep] at h
      cases h
      simp
    | three =>
      simp only [regStep] at h
      obtain ⟨d, m, hd, hv⟩ := ih u1 h
      refine ⟨d, m + 1, hd, ?_⟩
      rw [hv, List.replicate_succ']
      simp

/-- The second register of `w` is `u2`: `w` is `u2` followed by a letter `one` or `three`, then `m` letters `two`. -/
theorem regsAt_snd_shape (w u2 : Word) (h : (regsAt w).2 = some u2) :
    ∃ (d : Digit) (m : ℕ), (d = Digit.one ∨ d = Digit.three) ∧ w = u2 ++ [d] ++ List.replicate m Digit.two := by
  induction w using List.reverseRecOn generalizing u2 with
  | nil => simp [regsAt, regRun] at h
  | append_singleton v x ih =>
    rw [WeakStepPaper.regsAt_snoc] at h
    cases x with
    | one =>
      refine ⟨Digit.one, 0, Or.inl rfl, ?_⟩
      simp only [regStep] at h
      cases h
      simp
    | two =>
      simp only [regStep] at h
      obtain ⟨d, m, hd, hv⟩ := ih u2 h
      refine ⟨d, m + 1, hd, ?_⟩
      rw [hv, List.replicate_succ']
      simp
    | three =>
      refine ⟨Digit.three, 0, Or.inr rfl, ?_⟩
      simp only [regStep] at h
      cases h
      simp

end FLatticePaper.Tiles.SwapRegsShape
