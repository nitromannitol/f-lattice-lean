import FLatticePaper.Tiles.RowInterval

open FLatticePaper.Tiles

/-! Decided checks of the row-interval description, on the single cell and on the 1 × 2 rectangle. -/

-- the single cell: `w1 = [1]`, `w2 = [i]`
theorem single_cell_in : ((0 : ℤ), (0 : ℤ)) ∈ ({(0, 0)} : CellTile) := by
  rw [mem_iff_interval (T := ({(0, 0)} : CellTile)) (c := (0, 0)) (w1 := [.one]) (w2 := [.i])
    (by decide) (by decide) (by decide) 0 0]
  decide

theorem single_cell_out : ((1 : ℤ), (0 : ℤ)) ∉ ({(0, 0)} : CellTile) := by
  rw [mem_iff_interval (T := ({(0, 0)} : CellTile)) (c := (0, 0)) (w1 := [.one]) (w2 := [.i])
    (by decide) (by decide) (by decide) 1 0]
  decide

-- the 1 × 2 rectangle: `w1 = [1, 1]`, `w2 = [i]`
theorem rectangle_in : ((1 : ℤ), (0 : ℤ)) ∈ ({(0, 0), (1, 0)} : CellTile) := by
  rw [mem_iff_interval (T := ({(0, 0), (1, 0)} : CellTile)) (c := (0, 0)) (w1 := [.one, .one]) (w2 := [.i])
    (by decide) (by decide) (by decide) 1 0]
  decide

theorem rectangle_out : ((2 : ℤ), (0 : ℤ)) ∉ ({(0, 0), (1, 0)} : CellTile) := by
  rw [mem_iff_interval (T := ({(0, 0), (1, 0)} : CellTile)) (c := (0, 0)) (w1 := [.one, .one]) (w2 := [.i])
    (by decide) (by decide) (by decide) 2 0]
  decide

#print axioms mem_iff_interval
#print axioms sum_north
#print axioms sum_south
#print axioms single_cell_in
#print axioms rectangle_in
