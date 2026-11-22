import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.BaseCaseTiling

/-! The cell tiles of the reciprocal base tiles, for every denominator.

The vertex sets `stairF d = paperStairTile d` and `ladderF d = paperLadderTile d` (StandardTiles.lean) have cell tiles
`cellTileOf (stairF d)` and `cellTileOf (ladderF d)`: the cells whose four corners lie in the set. These are the repo's
cell sets `stairCells d` and `ladderCells d` (BaseCaseTiling.lean), for `d ≥ 3` and `d ≥ 4`. The repo's boundary lemmas
`stair_boundary_at` and `ladder_boundary_at` are about those cell sets, so these identities transfer them to the standard
base tiles. The proofs reduce each corner condition to linear integer arithmetic (`omega`). -/

namespace FLatticePaper.Tiles.BaseCellIdentities

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardClause

/-- A cell is in the cell tile of a vertex set iff it is in the set and its four corners are. -/
theorem mem_cellTileOf (P : Finset Site) (a : Site) : a ∈ cellTileOf P ↔ a ∈ P ∧ cellCorners a ⊆ P := by
  unfold cellTileOf
  rw [Finset.mem_filter]

/-- The four corners of the cell with lower-left corner `(x, y)` lie in `P` iff the four points do. -/
theorem cellCorners_subset_iff (P : Finset Site) (x y : Int) :
    cellCorners (x, y) ⊆ P ↔ (x, y) ∈ P ∧ (x + 1, y) ∈ P ∧ (x, y + 1) ∈ P ∧ (x + 1, y + 1) ∈ P := by
  simp only [cellCorners, Finset.insert_subset_iff, Finset.singleton_subset_iff, gOne, gI]
  have h1 : ((x, y) + (1, 0) : Site) = (x + 1, y) := by ext <;> simp
  have h2 : ((x, y) + (0, 1) : Site) = (x, y + 1) := by ext <;> simp
  have h3 : ((x, y) + ((1, 0) + (0, 1)) : Site) = (x + 1, y + 1) := by ext <;> simp
  rw [h1, h2, h3]

/-- The reciprocal staircase: the cell tile of `stairF d` is the repo's `stairCells d`, for `d ≥ 3`. -/
theorem cellTileOf_stairF (d : Int) (hd : 3 ≤ d) : cellTileOf (stairF d) = stairCells d := by
  ext ⟨x, y⟩
  rw [mem_cellTileOf, cellCorners_subset_iff, mem_stairCells d hd]
  simp only [stairF, stairInT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor <;> intro h <;> omega

/-- The doubled ladder: the cell tile of `ladderF d` is the repo's `ladderCells d`, for `d ≥ 4`. -/
theorem cellTileOf_ladderF (d : Int) (hd : 4 ≤ d) : cellTileOf (ladderF d) = ladderCells d := by
  ext ⟨x, y⟩
  rw [mem_cellTileOf, cellCorners_subset_iff, mem_ladderCells d hd]
  simp only [ladderF, ladderInT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor <;> intro h <;> omega

end FLatticePaper.Tiles.BaseCellIdentities
