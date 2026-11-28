import FLatticePaper.Tiles.MarksIn
import FLatticePaper.Tiles.BaseCellIdentities

/-! The base of the column propagation of the Step 1 of the stacked (d): the cells of a standard tile are invariant under its
half-turn, so the top cell of the tile over a column is the mirror of its lowest cell over the mirrored column. -/

namespace FLatticePaper.Tiles.StackedBase

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BaseCellIdentities

/-- **The cell half-turn.** A cell `(x, y)` of the odd standard tile gives the cell `(C.1 - x - 1, C.2 - y - 1)` of the same tile, where
`C = halfTurnCentre (oddTile w)`: the four corners of the mirrored cell are the half-turn images of the corners of the cell. -/
theorem cell_halfTurn_mem (w : Word) (x y : Int) (hc : ((x, y) : GInt) ∈ cellTileOf (oddTile w)) :
    (((halfTurnCentre (oddTile w)).1 - x - 1, (halfTurnCentre (oddTile w)).2 - y - 1) : GInt) ∈
      cellTileOf (oddTile w) := by
  have hT : ∀ z : GInt, z ∈ oddTile w →
      (((halfTurnCentre (oddTile w)).1 - z.1, (halfTurnCentre (oddTile w)).2 - z.2) : GInt) ∈ oddTile w :=
    fun z hz => MarksIn.halfTurn_oddTile w z hz
  obtain ⟨-, hsub⟩ := (mem_cellTileOf _ _).1 hc
  rw [cellCorners_subset_iff] at hsub
  obtain ⟨h0, h1, h2, h3⟩ := hsub
  rw [mem_cellTileOf]
  refine ⟨?_, ?_⟩
  · have := hT (x + 1, y + 1) h3
    convert this using 2 <;> ring
  · rw [cellCorners_subset_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hT (x + 1, y + 1) h3
      convert this using 2 <;> ring
    · have := hT (x, y + 1) h2
      convert this using 2 <;> ring
    · have := hT (x + 1, y) h1
      convert this using 2 <;> ring
    · have := hT (x, y) h0
      convert this using 2 <;> ring

end FLatticePaper.Tiles.StackedBase
