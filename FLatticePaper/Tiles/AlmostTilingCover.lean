import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.RowInterval

/-! Covering for `lemma:almost_square_tiling` (task 17): the covering clause of `IsAlmostTiling` is equivalent to
`Z² = T.vertices + L`, and the cells of a tile with boundary word `w1 w2 hat(rev w1) hat(rev w2)` are the row
intervals of `mem_iff_interval`. The general covering statement is not proved here; see the report. -/

namespace FLatticePaper.Tiles
open Finset

theorem mem_cellCorners_add_iff (x y v : GInt) : x ∈ cellCorners (y + v) ↔ x - v ∈ cellCorners y := by
  unfold cellCorners
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, gOne, gI]
  omega

/-- The covering clause of `IsAlmostTiling` in terms of the vertex set: every lattice point `x` has a translate
`x − v` (with `v` in the lattice) that is a vertex of `T`. -/
theorem covering_iff_vertices (L : Set GInt) (T : CellTile) :
    (∀ x : GInt, ∃ v ∈ L, ∃ y ∈ T, x ∈ cellCorners (y + v)) ↔
      (∀ x : GInt, ∃ v ∈ L, x - v ∈ T.vertices) := by
  constructor
  · intro h x
    obtain ⟨v, hv, y, hy, hx⟩ := h x
    refine ⟨v, hv, ?_⟩
    rw [CellTile.vertices, Finset.mem_biUnion]
    exact ⟨y, hy, (mem_cellCorners_add_iff x y v).mp hx⟩
  · intro h x
    obtain ⟨v, hv, hx⟩ := h x
    rw [CellTile.vertices, Finset.mem_biUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨v, hv, y, hy, (mem_cellCorners_add_iff x y v).mpr hxy⟩

/-- The cells of the tile whose boundary walk starts at `c` with the word `w1 w2 hat(rev w1) hat(rev w2)`, read off
row by row from `mem_iff_interval`, restricted to the window `[-B, B]²`. -/
def intervalCells (c : GInt) (w1 w2 : F2Word) (B : ℕ) : CellTile :=
  (window B).filter fun x =>
    (c.2 ≤ x.2 ∧ x.2 < c.2 + cntI (w1 ++ w2)) ∧
      colS (w1.map Unit4.neg ++ w2.map Unit4.neg) (c + F2Word.sum (w1 ++ w2)) x.2 ≤ x.1 ∧
      x.1 < colN (w1 ++ w2) c x.2

/-- On the window, the tile of a boundary word is the interval tile. -/
theorem mem_intervalCells_iff {T : CellTile} {c : GInt} {w1 w2 : F2Word} (B : ℕ)
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (x : GInt) (hx : x ∈ window B) :
    x ∈ T ↔ x ∈ intervalCells c w1 w2 B := by
  have key := mem_iff_interval hT h1 h2 x.1 x.2
  unfold intervalCells
  rw [Finset.mem_filter]
  refine ⟨fun hT' => ⟨hx, key.mp hT'⟩, fun h => key.mpr h.2⟩

-- The 2 × 2 square from `w1 = 1 1`, `w2 = i i`: the window check of the almost tiling conditions (decided).
theorem interval_square_window :
    WindowAlmostTiling (intervalCells 0 [.one, .one] [.i, .i] 3) (almostV₁ [.one, .one]) (almostV₂ [.i, .i]) 2 3 := by
  decide +kernel

-- `w1 = 1 1 1`, `w2 = i i`
theorem interval_one_one_one_window :
    WindowAlmostTiling (intervalCells 0 [.one, .one, .one] [.i, .i] 3) (almostV₁ [.one, .one, .one])
      (almostV₂ [.i, .i]) 2 3 := by
  decide +kernel

-- `w1 = 1 1`, `w2 = i (-1) i`
theorem interval_one_one_i_neg_one_i_window :
    WindowAlmostTiling (intervalCells 0 [.one, .one] [.i, .negOne, .i] 3) (almostV₁ [.one, .one])
      (almostV₂ [.i, .negOne, .i]) 2 3 := by
  decide +kernel

-- `w1 = 1 i 1`, `w2 = i i`
theorem interval_one_i_one_window :
    WindowAlmostTiling (intervalCells 0 [.one, .i, .one] [.i, .i] 3) (almostV₁ [.one, .i, .one])
      (almostV₂ [.i, .i]) 2 3 := by
  decide +kernel

-- `w1 = 1 1`, `w2 = i i i`
theorem interval_one_one_iii_window :
    WindowAlmostTiling (intervalCells 0 [.one, .one] [.i, .i, .i] 3) (almostV₁ [.one, .one])
      (almostV₂ [.i, .i, .i]) 2 3 := by
  decide +kernel
