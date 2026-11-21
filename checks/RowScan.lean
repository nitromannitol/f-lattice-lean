import FLatticePaper.Tiles.RowScan

open FLatticePaper.Tiles

/-! Checks of the row-scan lemma: the single cell has the count `-1` in its own column, and the count is the cell
indicator with a minus sign. -/

theorem single_cell_ind : cellInd ({(0, 0)} : CellTile) 0 0 = 1 := by decide

theorem single_cell_scan : rowCount ({(0, 0)} : CellTile).boundaryEdges 0 0 = -1 := by
  rw [row_scan, single_cell_ind]

#print axioms row_scan
#print axioms north_mem
#print axioms south_mem
#print axioms rowCount_eq
#print axioms single_cell_scan
