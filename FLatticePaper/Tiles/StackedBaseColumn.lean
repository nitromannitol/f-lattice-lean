import FLatticePaper.Tiles.StackedBottomLink
import FLatticePaper.Tiles.H3Pairs
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.StackedWalks

/-! The last column of the bottom walk and the cells over the column before it. When the bottom word ends with a horizontal unit
step, the walk meets its last column only at its end, so the cells of the tile over the column before the last one lie at or above
the end height. This is the lower bound of the top-cell reduction of the base of the column propagation. -/

namespace FLatticePaper.Tiles.StackedBaseColumn

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.OverlapSides FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.H3Pairs FLatticePaper.Tiles.CellExtremes

/-- Every point of a walk with letters `one` and `i` lies at or below its end componentwise. -/
theorem walk_le_end : ∀ (u : F2Word), (∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i) →
    ∀ (c b : GInt), b ∈ F2Word.walk c u → b.1 ≤ (c + F2Word.sum u).1 ∧ b.2 ≤ (c + F2Word.sum u).2 := by
  intro u
  induction u with
  | nil =>
    intro hu c b hb
    simp only [WalkDecomp.walk_nil, List.mem_singleton] at hb
    subst hb
    simp [F2Word.sum]
  | cons x u ih =>
    intro hu c b hb
    have hu' : ∀ y ∈ u, y = Unit4.one ∨ y = Unit4.i := fun y hy => hu y (by simp [hy])
    rw [WalkDecomp.walk_cons, List.mem_cons] at hb
    have hsum : c + F2Word.sum (x :: u) = (c + x.vec) + F2Word.sum u := by
      simp [F2Word.sum, add_assoc]
    rcases hb with hbc | hbt
    · rw [hbc]
      exact FLatticePaper.Tiles.StackedWalks.walk_ge_start (x :: u) hu c (c + F2Word.sum (x :: u))
        (FLatticePaper.Tiles.CellExtremes.mem_walk_last c (x :: u))
    · rw [hsum]
      exact ih hu' (c + x.vec) b hbt

/-- The walk of `u ++ [one]`: its only point over its last column is its end. -/
theorem walk_last_column (u : F2Word) (hu : ∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i) (b : GInt)
    (hb : b ∈ F2Word.walk (0, 0) (u ++ [Unit4.one])) (hbx : b.1 = (F2Word.sum (u ++ [Unit4.one])).1) :
    b = F2Word.sum (u ++ [Unit4.one]) := by
  have hs : (F2Word.sum (u ++ [Unit4.one])).1 = (F2Word.sum u).1 + 1 := by
    rw [f2sum_append]
    simp [F2Word.sum, Unit4.vec]
  rw [WalkDecomp.walk_append, List.mem_append] at hb
  rcases hb with hb | hb
  · have hle : b.1 ≤ (F2Word.sum u).1 := by simpa using (walk_le_end u hu (0, 0) b hb).1
    omega
  · rw [WalkDecomp.walk_cons, WalkDecomp.walk_nil] at hb
    simp only [List.tail_cons, List.mem_singleton] at hb
    rw [hb, f2sum_append, Prod.mk_zero_zero, zero_add]
    simp [F2Word.sum, Unit4.vec]

/-- **Cells over the column before the last one lie at or above the end height.** If the bottom word of the tile is `u ++ [one]`,
then a cell `(E1 - 1, y)` of the tile, where `E = sum (u ++ [one])`, has `E.2 ≤ y`. -/
theorem cell_above_end (P : Finset GInt) (w1 w2 : F2Word) (u : F2Word)
    (hT : IsBoundaryWordAt (cellTileOf P) (0, 0) (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = Unit4.one ∨ x = Unit4.i) (h2 : ∀ x ∈ w2, x = Unit4.i ∨ x = Unit4.negOne)
    (hw1 : w1 = u ++ [Unit4.one]) (y : Int)
    (hc : ((((F2Word.sum w1).1 - 1), y) : GInt) ∈ cellTileOf P) : (F2Word.sum w1).2 ≤ y := by
  subst hw1
  have hu : ∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i := fun x hx => h1 x (List.mem_append_left _ hx)
  have hcnt : cntI (u ++ [Unit4.one]) = (F2Word.sum (u ++ [Unit4.one])).2 :=
    (sum_snd_eq_cntI (u ++ [Unit4.one]) h1).symm
  have hrow := (mem_iff_nr hT h1 h2 ((F2Word.sum (u ++ [Unit4.one])).1 - 1) y).1 hc
  obtain ⟨⟨hy0, _⟩, _, hN⟩ := hrow
  have hy0' : 0 ≤ y := by simpa using hy0
  have hN' : (F2Word.sum (u ++ [Unit4.one])).1 - 1 < Nrow (0, 0) (u ++ [Unit4.one]) w2 y := by
    simpa using hN
  by_contra hlt
  push Not at hlt
  have hlt' : y < cntI (u ++ [Unit4.one]) := by omega
  rw [OverlapSides.nrow_lo hlt'] at hN'
  have hcol := col_on_bottom (u ++ [Unit4.one]) h1 y hy0' hlt'.le
  have hle : colN (u ++ [Unit4.one]) (0, 0) y ≤ (F2Word.sum (u ++ [Unit4.one])).1 := by
    simpa using (walk_le_end (u ++ [Unit4.one]) h1 (0, 0) _ hcol).1
  have hne : colN (u ++ [Unit4.one]) (0, 0) y ≠ (F2Word.sum (u ++ [Unit4.one])).1 := by
    intro heq
    have hb := walk_last_column u hu ((colN (u ++ [Unit4.one]) (0, 0) y, y) : GInt) hcol
      (by simpa using heq)
    have hy2 := congrArg Prod.snd hb
    simp only at hy2
    omega
  have hlt2 : colN (u ++ [Unit4.one]) (0, 0) y < (F2Word.sum (u ++ [Unit4.one])).1 := lt_of_le_of_ne hle hne
  omega

/-- The odd bottom word ends with the horizontal unit step: `oddBottom w = u ++ [one]`, from the bottom word of the horizontal
word (`RegisterLink.oddBottom_eq_gH`). -/
theorem oddBottom_snoc (w : Word) : ∃ u : F2Word, FLatticePaper.Tiles.StandardBoundary.oddBottom w = u ++ [Unit4.one] :=
  ⟨_, FLatticePaper.Tiles.RegisterLink.oddBottom_eq_gH w⟩

end FLatticePaper.Tiles.StackedBaseColumn
