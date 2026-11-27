import FLatticePaper.Tiles.SeamSymm
import FLatticePaper.Tiles.BoundaryWalks
import FLatticePaper.Tiles.NeighbourDisjoint
import FLatticePaper.Tiles.OverlapSides
import FLatticePaper.Tiles.StandardBoundary

/-! The column form of a standard tile, from its row form by the quarter turn. A cell `p` lies in `cellTileOf P` exactly when
the turned cell `rotC p - a` lies in `cellTileOf Q`, when `rot P = shift Q a` (the rotation of the odd standard tile is a
translate of the even standard tile of the swapped word, `rot_standard_tiles`). So a column of `P` is a row of `Q`, and the row
form `mem_iff_nr` of `Q` gives the column form of `P`. -/

namespace FLatticePaper.Tiles.StackedColumnFacts

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BoundaryTransport FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary

/-- **Cells of a rotated translate.** If `rot P = shift Q a`, a cell `p` lies in `P` exactly when `rotC p - a` lies in `Q`. -/
theorem cell_iff_rot_shift (P Q : Tile) (a : GInt) (hrot : rot P = shift Q a) (p : GInt) :
    p ∈ cellTileOf P ↔ rotC p - a ∈ cellTileOf Q := by
  have h : cellTileOf (rot P) = cellTileOf (shift Q a) := by rw [hrot]
  rw [SeamSymm.cellTileOf_rot, SeamSymm.cellTileOf_shift] at h
  have key : rotC p ∈ rotCells (cellTileOf P) ↔ p ∈ cellTileOf P := by
    rw [mem_rotCells, rotCInv_rotC]
  rw [← key, h, BoundaryWalks.mem_image_add_iff]

/-- **The column form of a standard tile, from its row form.** If `rot P = shift Q a` and `Q` has the boundary word `boundaryWordOf w1 w2`
from the origin, then a cell `(t, y)` of `P` lies over column `t` exactly when the row `t - a.2` of `Q` contains `-y - 1 - a.1`. -/
theorem column_iff_row {Q : Tile} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt (cellTileOf Q) (0, 0) (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = Unit4.one ∨ x = Unit4.i) (h2 : ∀ x ∈ w2, x = Unit4.i ∨ x = Unit4.negOne)
    (P : Tile) (a : GInt) (hrot : rot P = shift Q a) (t y : ℤ) :
    ((t, y) : GInt) ∈ cellTileOf P ↔
      (0 ≤ t - a.2 ∧ t - a.2 < cntI w1 + cntI w2) ∧
        Srow (0, 0) w1 w2 (t - a.2) ≤ -y - 1 - a.1 ∧ -y - 1 - a.1 < Nrow (0, 0) w1 w2 (t - a.2) := by
  rw [cell_iff_rot_shift P Q a hrot]
  have e : rotC (t, y) - a = (-y - 1 - a.1, t - a.2) := by
    ext <;> simp [rotC]
  rw [e]
  have h := mem_iff_nr hT h1 h2 (-y - 1 - a.1) (t - a.2)
  simpa using h

/-- **The column form of the odd standard tile.** The quarter turn of `oddTile w` is a translate `shift (evenTile (swapW w)) a`
(`rot_standard_tiles`), so the columns of the odd tile are the rows of the even tile of the swapped word. -/
theorem odd_column_iff (w : Word) (a : GInt) (hrot : rot (oddTile w) = shift (evenTile (swapW w)) a) (t y : ℤ) :
    ((t, y) : GInt) ∈ cellTileOf (oddTile w) ↔
      (0 ≤ t - a.2 ∧ t - a.2 < cntI (evenBottom (swapW w)) + cntI (evenRight (swapW w))) ∧
        Srow (0, 0) (evenBottom (swapW w)) (evenRight (swapW w)) (t - a.2) ≤ -y - 1 - a.1 ∧
        -y - 1 - a.1 < Nrow (0, 0) (evenBottom (swapW w)) (evenRight (swapW w)) (t - a.2) :=
  column_iff_row (OverlapSides.boundary_even (swapW w)) (StandardBoundary.admissible_evenStandard (swapW w)).1.1
    (OverlapSides.letters_w2 (StandardBoundary.admissible_evenStandard (swapW w)).2) (oddTile w) a hrot t y

end FLatticePaper.Tiles.StackedColumnFacts
