import FLatticePaper.Tiles.StandardClauseA

/-! Task 55 (R1), bridge from point rows to cell rows, as a separate lemma. A cell `(x, b)` of `cellTileOf C` is a point of `C`
whose four corners `(x,b), (x+1,b), (x,b+1), (x+1,b+1)` lie in `C`. If the rows of `C` are intervals `[lo c, hi c)`, the cell
row `b` is the interval `[max (lo b) (lo (b+1)), min (hi b) (hi (b+1)) - 1)`. -/

namespace FLatticePaper.Tiles.CellRowBridge

open FLatticePaper FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause

theorem mem_cellTileOf_iff (C : Finset Site) (lo hi : ℤ → ℤ)
    (hC : ∀ x c : ℤ, ((x, c) : Site) ∈ C ↔ lo c ≤ x ∧ x < hi c) (x b : ℤ) :
    ((x, b) : GInt) ∈ cellTileOf C ↔
      max (lo b) (lo (b + 1)) ≤ x ∧ x + 1 < min (hi b) (hi (b + 1)) := by
  simp only [cellTileOf, Finset.mem_filter, cellCorners, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, hC, gOne, gI, Prod.mk_add_mk, add_zero, zero_add]
  omega

end FLatticePaper.Tiles.CellRowBridge
