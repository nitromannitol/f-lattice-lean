import FLatticePaper.Tiles.EdgeClause
import FLatticePaper.Tiles.AlmostTilingCover

/-! Assembly of `lemma:almost_square_tiling`. The almost tiling condition has two parts: uniqueness of the cell-translates
(proved from the neighbour disjointness and the first-crossing input `NoFirstCrossing`), and the covering clause, which
is the hypothesis `hC` below (not yet proved; see the report). The edge clause is proved from `NoFarAdjacency`. The two
global inputs of the paper, and the covering clause, are explicit hypotheses of the theorem. -/

namespace FLatticePaper.Tiles

/-- The almost square tiling lemma, assembled: for a simple tile with boundary word `w1 w2 hat(rev w1) hat(rev w2)` and
admissible `w1`, `-i w2`, the tile generates the `(Σw1 + i, Σw2 - 1)`-regular almost tiling, and the only translates
sharing an edge with it are `± (Σw1 + i)` and `± (Σw2 - 1)`. -/
theorem almost_square_tiling {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (_hT : IsSimpleTile T) (hB : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI))
    (hC : ∀ x : GInt, ∃ v ∈ latticeOf (almostV₁ w1) (almostV₂ w2), ∃ y ∈ T, x ∈ cellCorners (y + v))
    (hF : NoFirstCrossing T (almostV₁ w1) (almostV₂ w2))
    (hG : NoFarAdjacency T (almostV₁ w1) (almostV₂ w2)) :
    IsRegularAlmostTiling T (almostV₁ w1) (almostV₂ w2) ∧ EdgeSharingClause T (almostV₁ w1) (almostV₂ w2) := by
  have hN := neighbour_disjoint hB hA1 hA2
  have hU := uniqueness_of_neighbours hN hF
  exact ⟨⟨hU, hC⟩, edge_clause hB hA1 hA2 hF hG⟩

end FLatticePaper.Tiles
