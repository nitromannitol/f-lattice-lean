import FLatticePaper.Tiles.CeilWords

/-! The decomposition table of clause (d) (Step 3 of `lemma:standard_tile_properties`), as identities of the Farey quadruples.

For a word `u` with parents `A = parentP u` and `B = parentQ u`, and the child `u * s`, the parents of `u * s` are
`(childP u, childQ u)` for `s = one`, `(childP u, B)` for `s = two` and `(A, childQ u)` for `s = three`. The six identities are the
rows of the table: for the column given by the parity of the number of ones in `u` (the phase of the child `u * s` is the
parity of `u` for `s = two, three`, and its complement for `s = one`), the first word of the interface is `P` or `QQ` and the
second is `Q`, `QQ` or `P`, where `P` and `Q` are the parents of `u * s`. -/

namespace FLatticePaper.Tiles.StackedTable

open FLatticePaper.Tiles FLatticePaper.Farey

/-- The child pair of a word is the child formula of the quadruple recursion. -/
theorem quad_childs (u : Word) :
    (quadAt [] u).childP = (childWords u (quadAt [] u).parentP (quadAt [] u).parentQ).1 ∧
    (quadAt [] u).childQ = (childWords u (quadAt [] u).parentP (quadAt [] u).parentQ).2 := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton u d _ =>
    rw [CeilWords.quadAt_snoc_nil]
    cases d <;> simp [WordQuad.step, childWords]

theorem parentP_snoc_one (u : Word) : (quadAt [] (u ++ [Digit.one])).parentP = (quadAt [] u).childP := by
  rw [CeilWords.quadAt_snoc_nil]; rfl

theorem parentQ_snoc_one (u : Word) : (quadAt [] (u ++ [Digit.one])).parentQ = (quadAt [] u).childQ := by
  rw [CeilWords.quadAt_snoc_nil]; rfl

theorem parentP_snoc_two (u : Word) : (quadAt [] (u ++ [Digit.two])).parentP = (quadAt [] u).childP := by
  rw [CeilWords.quadAt_snoc_nil]; rfl

theorem parentQ_snoc_two (u : Word) : (quadAt [] (u ++ [Digit.two])).parentQ = (quadAt [] u).parentQ := by
  rw [CeilWords.quadAt_snoc_nil]; rfl

theorem parentP_snoc_three (u : Word) : (quadAt [] (u ++ [Digit.three])).parentP = (quadAt [] u).parentP := by
  rw [CeilWords.quadAt_snoc_nil]; rfl

theorem parentQ_snoc_three (u : Word) : (quadAt [] (u ++ [Digit.three])).parentQ = (quadAt [] u).childQ := by
  rw [CeilWords.quadAt_snoc_nil]; rfl

/-- Row `s = one`, even-first column: `P = Q v` with `v = B`. -/
theorem row1_even (u : Word) (hu : u.count .one % 2 = 1) :
    (quadAt [] (u ++ [Digit.one])).parentP =
      (quadAt [] (u ++ [Digit.one])).parentQ ++ (quadAt [] u).parentQ := by
  rw [parentP_snoc_one, parentQ_snoc_one, (quad_childs u).1, (quad_childs u).2]
  simp [childWords, hu, List.append_assoc]

/-- Row `s = one`, odd-first column: `P = v Q` with `v = B`. -/
theorem row1_odd (u : Word) (hu : u.count .one % 2 = 0) :
    (quadAt [] (u ++ [Digit.one])).parentP =
      (quadAt [] u).parentQ ++ (quadAt [] (u ++ [Digit.one])).parentQ := by
  rw [parentP_snoc_one, parentQ_snoc_one, (quad_childs u).1, (quad_childs u).2]
  simp [childWords, hu, List.append_assoc]

/-- Row `s = two`, even-first column: `P = Q Q u` with `Q = B` and `u = A`. -/
theorem row2_even (u : Word) (hu : u.count .one % 2 = 0) :
    (quadAt [] (u ++ [Digit.two])).parentP =
      (quadAt [] (u ++ [Digit.two])).parentQ ++ (quadAt [] (u ++ [Digit.two])).parentQ ++ (quadAt [] u).parentP := by
  rw [parentP_snoc_two, parentQ_snoc_two, (quad_childs u).1]
  simp [childWords, hu, List.append_assoc]

/-- Row `s = two`, odd-first column: `P = u Q Q` with `Q = B` and `u = A`. -/
theorem row2_odd (u : Word) (hu : u.count .one % 2 = 1) :
    (quadAt [] (u ++ [Digit.two])).parentP =
      (quadAt [] u).parentP ++ (quadAt [] (u ++ [Digit.two])).parentQ ++ (quadAt [] (u ++ [Digit.two])).parentQ := by
  rw [parentP_snoc_two, parentQ_snoc_two, (quad_childs u).1]
  simp [childWords, hu, List.append_assoc]

/-- Row `s = three`, even-first column: `X = P` and `Y = Q v P` is `Q Q`. -/
theorem row3_even (u : Word) (hu : u.count .one % 2 = 0) :
    (quadAt [] (u ++ [Digit.three])).parentQ ++ (quadAt [] u).parentQ ++
        (quadAt [] (u ++ [Digit.three])).parentP =
      (quadAt [] (u ++ [Digit.three])).parentQ ++ (quadAt [] (u ++ [Digit.three])).parentQ := by
  rw [parentP_snoc_three, parentQ_snoc_three, (quad_childs u).2]
  simp [childWords, hu, List.append_assoc]

/-- Row `s = three`, odd-first column: `X = P v Q` is `Q Q`. -/
theorem row3_odd (u : Word) (hu : u.count .one % 2 = 1) :
    (quadAt [] (u ++ [Digit.three])).parentP ++ (quadAt [] u).parentQ ++
        (quadAt [] (u ++ [Digit.three])).parentQ =
      (quadAt [] (u ++ [Digit.three])).parentQ ++ (quadAt [] (u ++ [Digit.three])).parentQ := by
  rw [parentP_snoc_three, parentQ_snoc_three, (quad_childs u).2]
  simp [childWords, hu, List.append_assoc]

end FLatticePaper.Tiles.StackedTable
