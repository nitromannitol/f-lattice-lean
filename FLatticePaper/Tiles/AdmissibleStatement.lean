import FLatticePaper.Tiles.AdmissibleFinal

/-! Task 51: the admissibility hypotheses of `almost_square_tiling` for the bottom-edge words. For the recursion word
`word`, the boundary pair is `w₁ = (bottomEdges word).2` and `w₂ = (bottomEdges (word.map swapTwoThree)).1.map mulI`,
so that `w₂.map mulNegI` is the odd edge of the swapped word. -/

namespace FLatticePaper.Tiles
open Farey

theorem mulNegI_mulI_list (w : F2Word) : (w.map Unit4.mulI).map Unit4.mulNegI = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.map_cons, List.map_cons, ih]
    congr 1
    cases x <;> rfl

/-- The two admissibility conditions of `almost_square_tiling` for the bottom-edge words of any recursion word. -/
theorem bottomEdges_admissible_pair (word : Word) :
    Admissible (bottomEdges word).2 ∧
      Admissible (((bottomEdges (word.map Digit.swapTwoThree)).1.map Unit4.mulI).map Unit4.mulNegI) := by
  rw [mulNegI_mulI_list]
  exact ⟨(bottomEdges_admissible word).2, (bottomEdges_admissible _).1⟩

end FLatticePaper.Tiles
