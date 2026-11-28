import FLatticePaper.Tiles.StackedBottomLink
import FLatticePaper.Tiles.StackedBase
import FLatticePaper.Tiles.StackedBaseCentre
import FLatticePaper.Tiles.StackedBaseColumn
import FLatticePaper.Tiles.CellExtremes
import FLatticePaper.Tiles.StackedWalks
import FLatticePaper.Tiles.BaseCellIdentities

/-! The base of the column propagation of the stacked (d), at column `1`. Let `v = texV2 (fracOdd w)` and let the odd tile be `T`.
The translate `T - v` lies below `T` in every common column; the propagation starts at column `1`, where:
* every cell of `T` over column `1` lies at height `0` or above (`odd_column_one_low`, from the lower link of the bottom walk);
* every cell of `T` over column `1 + v.1` lies at height `v.2 - 1` or below (`odd_column_one_high`, from the cell half-turn of
  `T` about `halfTurnCentre`, which sends column `1 + v.1` to the column before the last one of the bottom walk, where the cells
  lie at or above the end height of the bottom walk, `StackedBaseColumn.cell_above_end`). A cell `(1, y)` of `T - v` is the cell
  `(1 + v.1, y + v.2)` of `T`, so `T - v` has all its cells over column `1` at height `-1` or below. -/

namespace FLatticePaper.Tiles.StackedBaseOrder

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.CellExtremes FLatticePaper.Tiles.BaseCellIdentities

/-- **The cells of the odd tile over column `1` lie at height `0` or above.** A cell `(1, y)` has the site `(1, y)` of the tile, and
the lower link of the bottom walk gives a point `(1, h)` of the walk with `h ≤ y`; the walk from `(0, 0)` stays at or above
`(0, 0)`, so `0 ≤ h ≤ y`. The first column of the bottom walk is at least `1`, because `oddBottom w` ends with the horizontal step
`one` (`StackedBaseColumn.oddBottom_snoc`). -/
theorem odd_column_one_low (w : Word) (y : ℤ) (hc : ((1, y) : GInt) ∈ cellTileOf (oddTile w)) : 0 ≤ y := by
  obtain ⟨u, hu⟩ := StackedBaseColumn.oddBottom_snoc w
  have hsite : ((1, y) : GInt) ∈ oddTile w := ((mem_cellTileOf _ _).1 hc).1
  have hwb : ∀ x ∈ oddBottom w, x = Unit4.one ∨ x = Unit4.i := (admissible_oddStandard w).1.1
  have hu' : ∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i := fun x hx =>
    (admissible_oddStandard w).1.1 x (by rw [hu]; exact List.mem_append_left _ hx)
  have hsum : (F2Word.sum (oddBottom w)).1 = (F2Word.sum u).1 + 1 := by
    rw [hu]
    simp [F2Word.sum, List.map_append, List.sum_append, Unit4.vec]
  have hu0 : 0 ≤ (F2Word.sum u).1 := by
    have hm := mem_walk_last ((0, 0) : GInt) u
    have h := (StackedWalks.walk_ge_start u hu' (0, 0) _ hm).1
    simpa using h
  obtain ⟨h, hh, hmem⟩ := StackedBottomLink.odd_lower_link w (1, y) hsite 1 rfl (by norm_num) (by rw [hsum]; omega)
  have hw := (StackedWalks.walk_ge_start (oddBottom w) hwb (0, 0) _ hmem).2
  have h0 : (0 : ℤ) ≤ h := by simpa using hw
  omega

/-- **The cells of the translate `T - v` over column `1` lie at height `-1` or below.** A cell of `T` over the column `1 + v.1`
has height `v.2 - 1` or below: its mirror image under the cell half-turn (`StackedBase.cell_halfTurn_mem`) is a cell of `T` over
the column `C.1 - (1 + v.1) - 1 = E.1 - 1`, where `E = sum (oddBottom w)` and `C = halfTurnCentre (oddTile w)`, and there the cells
lie at or above the end height `E.2` (`StackedBaseColumn.cell_above_end`). Since `C.2 = E.2 + v.2`, this gives the bound. -/
theorem odd_column_one_high (w : Word) (y : ℤ)
    (hc : ((1 + (texV2 (fracOdd w)).1, y + (texV2 (fracOdd w)).2) : GInt) ∈ cellTileOf (oddTile w)) : y ≤ -1 := by
  obtain ⟨u, hu⟩ := StackedBaseColumn.oddBottom_snoc w
  obtain ⟨hC1, hC2⟩ := StackedBaseCentre.centre_odd_coords w
  have hm := StackedBase.cell_halfTurn_mem w (1 + (texV2 (fracOdd w)).1) (y + (texV2 (fracOdd w)).2) hc
  have hm' : (((F2Word.sum (oddBottom w)).1 - 1, (halfTurnCentre (oddTile w)).2 - (y + (texV2 (fracOdd w)).2) - 1) : GInt) ∈
      cellTileOf (oddTile w) := by
    have e1 : (halfTurnCentre (oddTile w)).1 - (1 + (texV2 (fracOdd w)).1) - 1 = (F2Word.sum (oddBottom w)).1 - 1 := by
      omega
    rw [← e1]
    exact hm
  have hab := StackedBaseColumn.cell_above_end (oddTile w) (oddBottom w) (oddRight w) u (OverlapSides.boundary_odd w)
    (admissible_oddStandard w).1.1 (OverlapSides.letters_w2 (admissible_oddStandard w).2) hu _ hm'
  omega

end FLatticePaper.Tiles.StackedBaseOrder
