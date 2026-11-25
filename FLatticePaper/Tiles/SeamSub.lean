import FLatticePaper.Tiles.SubOddCopy
import FLatticePaper.Tiles.SubEvenCopy
import FLatticePaper.Tiles.RightSub

/-! Task Q25 (sub), the `sub` fields of the seam for every word.

The bottom walk of the odd (resp. even) child lies on the boundary of its tile (`bottomCopyOdd_all`, `bottomCopyEven_all`). The right
walk of the odd (resp. even) child lies on the boundary by `RightSub.right_sub_odd` (resp. `right_sub_even`), which takes the bottom copy
of the swapped word (`swapW`). Together these give the `sub` field of `BottomSeamOdd` and `BottomSeamEven` for every word. -/

namespace FLatticePaper.Tiles.SeamSub

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SubOddCopy FLatticePaper.Tiles.SubEvenCopy FLatticePaper.Tiles.RightSub

/-- The `sub` field of the odd seam: the odd bottom walk and the odd right walk lie on the boundary of the odd tile. -/
theorem subOdd_all (u : Word) :
    ∀ e ∈ edgesFrom 0 (oddBottom u) ++ edgesFrom (F2Word.sum (oddBottom u)) (oddRight u),
      e ∈ (cellTileOf (oddTile u)).boundaryEdges := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact bottomCopyOdd_all u e h
  · exact right_sub_odd u (bottomCopyEven_all (swapW u)) e h

/-- The `sub` field of the even seam: the even bottom walk and the even right walk lie on the boundary of the even tile. -/
theorem subEven_all (u : Word) :
    ∀ e ∈ edgesFrom 0 (evenBottom u) ++ edgesFrom (F2Word.sum (evenBottom u)) (evenRight u),
      e ∈ (cellTileOf (evenTile u)).boundaryEdges := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact bottomCopyEven_all u e h
  · exact right_sub_even u (bottomCopyOdd_all (swapW u)) e h

end FLatticePaper.Tiles.SeamSub
