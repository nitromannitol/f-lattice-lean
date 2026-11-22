import FLatticePaper.Tiles.RecursionIdentity
import FLatticePaper.Tiles.StandardTiles

/-! The registers of the standard tiles and of the bottom edges agree (TeX 2723, step 2).

The tile registers `(stateAt u).tOdd`, `(stateAt u).tEven` of the standard recursion hold the tiles of the sources
`srcOf u` of the bottom-edge registers (`RecursionIdentity.lean`). With the recursion of the bottom edges, the bottom
edges of the child at `u` are one `edgeStep` of the bottom edges of the two source tiles. -/

namespace FLatticePaper.Tiles.RegisterTiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.RecursionIdentity

/-- The odd tile register is the odd tile of the odd source, once `1` or `2` has occurred. -/
theorem tOdd_eq_oddTile (u : Word) : (∃ y ∈ u, y = Digit.one ∨ y = Digit.two) →
    (stateAt u).tOdd = oddTile (srcOf u).1 := by
  induction u using List.reverseRecOn with
  | nil => intro h; simp at h
  | append_singleton u x ih =>
    intro h
    have hsrc := srcFrom_snoc x [] u ([], [])
    unfold srcOf
    rw [hsrc]
    cases x with
    | one =>
      rw [tOdd_snoc_one]
      simp
    | two =>
      rw [tOdd_snoc_two]
      simp
    | three =>
      have h' : ∃ y ∈ u, y = Digit.one ∨ y = Digit.two := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      rw [tOdd_snoc_three, ih h']
      simp only [srcOf]
      simp

/-- The even tile register is the even tile of the even source, once `1` or `3` has occurred. -/
theorem tEven_eq_evenTile (u : Word) : (∃ y ∈ u, y = Digit.one ∨ y = Digit.three) →
    (stateAt u).tEven = evenTile (srcOf u).2 := by
  induction u using List.reverseRecOn with
  | nil => intro h; simp at h
  | append_singleton u x ih =>
    intro h
    have hsrc := srcFrom_snoc x [] u ([], [])
    unfold srcOf
    rw [hsrc]
    cases x with
    | one =>
      rw [tEven_snoc_one]
      simp
    | two =>
      have h' : ∃ y ∈ u, y = Digit.one ∨ y = Digit.three := by
        obtain ⟨y, hy, hy'⟩ := h
        rcases List.mem_append.mp hy with hy | hy
        · exact ⟨y, hy, hy'⟩
        · simp at hy
          subst hy
          simp at hy'
      rw [tEven_snoc_two, ih h']
      simp only [srcOf]
      simp
    | three =>
      rw [tEven_snoc_three]
      simp

/-- The bottom edges of a non-base child are one `edgeStep` of the bottom edges of its two source words; with
`oddBottom`/`evenBottom` written for the bottom edges, this is the recursion of the tiles' bottom edges. -/
theorem oddBottom_rec (u : Word) (hT : allTwos u = false) (hH : allThrees u = false) :
    (bottomEdges u).1 =
      if u.count Digit.one % 2 = 1 then
        (bottomEdges (srcOf u).1).1 ++ [Unit4.i] ++ (bottomEdges (srcOf u).2).2 ++ [Unit4.i] ++
          (bottomEdges (srcOf u).2).2
      else
        (bottomEdges (srcOf u).2).2 ++ [Unit4.i] ++ (bottomEdges (srcOf u).2).2 ++ [Unit4.i] ++
          (bottomEdges (srcOf u).1).1 := by
  rw [bottomEdges_rec u hT hH]
  by_cases h : u.count Digit.one % 2 = 1
  · have h' : (u.count Digit.one % 2 == 1) = true := by simpa using h
    simp [edgeStep, h]
  · have h' : (u.count Digit.one % 2 == 1) = false := by simpa using h
    simp [edgeStep, h, h']

end FLatticePaper.Tiles.RegisterTiles
