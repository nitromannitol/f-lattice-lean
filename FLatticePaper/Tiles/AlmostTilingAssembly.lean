import FLatticePaper.Tiles.EdgeClause
import FLatticePaper.Tiles.AlmostTilingCover
import FLatticePaper.Tiles.CoveringRows
import FLatticePaper.Tiles.SuccessorProof

/-! Assembly of `lemma:almost_square_tiling`. The almost tiling condition has two parts: uniqueness of the cell-translates
(proved from the neighbour disjointness and the first-crossing input `NoFirstCrossing`), and the covering clause, which
is proved from the successor condition `SuccCover` (proved from the edge-connectivity of the tile, which is part of
`IsSimpleTile`, Sec. 4 line 724). The edge clause is proved from `NoFarAdjacency`. The two named global inputs of the
paper are the explicit hypotheses of the theorem. -/

namespace FLatticePaper.Tiles

/-- The admissible word `w1` and `-i w2` give `1 ≤ cntI w2`: the head of `-i w2` is `1`, so `w2` begins with `i`. -/
theorem cntI_w2_pos {w2 : F2Word} (hA2 : Admissible (w2.map Unit4.mulNegI)) : 1 ≤ cntI w2 := by
  obtain ⟨-, hhead, -, -⟩ := hA2
  cases w2 with
  | nil => simp at hhead
  | cons x w2' =>
    have hn := cntI_nonneg w2'
    cases x <;> simp [Unit4.mulNegI, Unit4.mulI, cntI] at hhead ⊢
    all_goals omega

/-- The almost square tiling lemma, assembled: for a simple tile with boundary word `w1 w2 hat(rev w1) hat(rev w2)` and
admissible `w1`, `-i w2`, the tile generates the `(Σw1 + i, Σw2 - 1)`-regular almost tiling, and the only translates
sharing an edge with it are `± (Σw1 + i)` and `± (Σw2 - 1)`. The successor condition `SuccCover` (the combinatorial
interface lemma of the covering, to be proved) and the two global inputs are explicit hypotheses. -/
theorem almost_square_tiling {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsSimpleTile T) (hB : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI))
    (hF : NoFirstCrossing T (almostV₁ w1) (almostV₂ w2))
    (hG : NoFarAdjacency T (almostV₁ w1) (almostV₂ w2)) :
    IsRegularAlmostTiling T (almostV₁ w1) (almostV₂ w2) ∧ EdgeSharingClause T (almostV₁ w1) (almostV₂ w2) := by
  obtain ⟨-, hE⟩ := hT
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have hmono : ∀ y ∈ w2.map Unit4.mulNegI, y = .one ∨ y = .i := hA2.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hmono x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  have hN := neighbour_disjoint hB hA1 hA2
  have hU := uniqueness_of_neighbours hN hF
  have hS := succCover_proved hB hE hA1 hA2
  have hC := covering_clause_of_succ hB h1 h2 (cntI_w2_pos hA2) hS
  exact ⟨⟨hU, hC⟩, edge_clause hB hA1 hA2 hF hG⟩

end FLatticePaper.Tiles
