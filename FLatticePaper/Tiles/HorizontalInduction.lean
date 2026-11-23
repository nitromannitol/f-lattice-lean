import FLatticePaper.Tiles.HorizontalStep

/-! Task 53, marksIn (horizontal induction): the forward horizontal strings of every standard tile lie in the tile.

`HorizontalStep.inv_step_one/two/three` give the invariant `Inv` for every non-base word from the invariant of its prefix. The
base words (`[]`, `3^n`, `2^n` with `n ≥ 1`) start the induction; they are the hypotheses `hNil`, `hThree`, `hTwo` below. -/

namespace FLatticePaper.Tiles.HorizontalInduction

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.HorizontalStep FLatticePaper.Tiles.HorizontalGlue

/-- The invariant of every word, from the invariant of the base words. -/
theorem inv_all (hNil : Inv []) (hThree : ∀ n : ℕ, 1 ≤ n → Inv (List.replicate n Digit.three))
    (hTwo : ∀ n : ℕ, 1 ≤ n → Inv (List.replicate n Digit.two)) (w : Word) : Inv w := by
  induction w using List.reverseRecOn with
  | nil => exact hNil
  | append_singleton v d ih =>
    cases d with
    | one => exact inv_step_one v ih
    | two =>
      by_cases hv : ∀ x ∈ v, x = Digit.two
      · have e : v ++ [Digit.two] = List.replicate (v.length + 1) Digit.two := by
          refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
          rcases List.mem_append.1 hx with h | h
          · exact hv x h
          · simp at h
            exact h
        rw [e]
        exact hTwo _ (by omega)
      · exact inv_step_two v ih hv
    | three =>
      by_cases hv : ∀ x ∈ v, x = Digit.three
      · have e : v ++ [Digit.three] = List.replicate (v.length + 1) Digit.three := by
          refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
          rcases List.mem_append.1 hx with h | h
          · exact hv x h
          · simp at h
            exact h
        rw [e]
        exact hThree _ (by omega)
      · exact inv_step_three v ih hv

/-- The horizontal strings of every standard tile lie in the tile: the odd string in `oddTile`, the even string in `evenTile`. -/
theorem horizontal_all (hNil : Inv []) (hThree : ∀ n : ℕ, 1 ≤ n → Inv (List.replicate n Digit.three))
    (hTwo : ∀ n : ℕ, 1 ≤ n → Inv (List.replicate n Digit.two)) (w : Word) :
    HC (quadAt [] w).childP (oddTile w) ∧ HC (quadAt [] w).childQ (evenTile w) :=
  ⟨(inv_all hNil hThree hTwo w).1, (inv_all hNil hThree hTwo w).2.1⟩

end FLatticePaper.Tiles.HorizontalInduction
