import FLatticePaper.Tiles.BottomSeamAll
import FLatticePaper.Tiles.StandardPacking
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.DeckCoverage

/-! Task Q25, assembly: `StandardBoundaryWord u` for every word `u` (`standardBoundaryWord_all`, from the two seams of
`BottomSeamAll`), and the statements that took it as an input, now without it: the simplicity and packing fields of clause (a),
clause (a) for the odd and even tiles and its edge clause for the odd tile, and the covering of the odd and even standard tiles
by their modified decks.

What `StandardBoundaryWord u` carries: only the decomposition, that the cell tile of each tile has the boundary word
`boundaryWordOf w1 w2` from `(0, 0)` (`StandardBoundaryOdd`, `StandardBoundaryEven`). The other inputs of `almost_square_tiling`
(simplicity, the admissibility of `w1` and of `w2.map mulNegI`, the two packing inequalities) and the two sums
(`almostV₁ w1 = texV1`, `almostV₂ w2 = texV2`, with `almostV₁ w = F2Word.sum w + gI` and `almostV₂ w = F2Word.sum w − gOne`)
are separate theorems. `boundaryTilingOdd_all` and `boundaryTilingEven_all` bundle all of them, for every word, so the full
boundary-tiling clause (2723 part 2) is `boundaryTilingOdd_all` and `boundaryTilingEven_all`. -/

namespace FLatticePaper.Tiles.StandardAll

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardSimple
open FLatticePaper.Tiles.DeckCoverage FLatticePaper.Tiles.StandardDischarge FLatticePaper.Tiles.BottomSeamAll

/-- `StandardBoundaryWord u` for every word `u`, from the two bottom seams of `u`. -/
theorem standardBoundaryWord_all (u : Word) : StandardBoundaryWord u :=
  BottomSeam.standardBoundaryWord_of_seams u (bottomSeamOdd_all u) (bottomSeamEven_all u)

/-- The odd standard tile is simple, for every word. -/
theorem simpleOdd_all (w : Word) : IsSimpleTile (cellTileOf (oddTile w)) :=
  simpleOdd_of_standardBoundaryWord standardBoundaryWord_all w

/-- The even standard tile is simple, for every word. -/
theorem simpleEven_all (w : Word) : IsSimpleTile (cellTileOf (evenTile w)) :=
  simpleEven_of_standardBoundaryWord standardBoundaryWord_all w

/-- The packing fields of the odd standard tile, for every word. -/
theorem packOdd_all (w : Word) :
    NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) :=
  packOdd_of_standardBoundaryWord standardBoundaryWord_all w

/-- The packing fields of the even standard tile, for every word. -/
theorem packEven_all (w : Word) :
    NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) :=
  packEven_of_standardBoundaryWord standardBoundaryWord_all w

/-- The standard inputs of clause (a), with no boundary-word and no packing hypothesis. -/
def standardInputsAll : StandardInputs := standardInputsOfBoundary standardBoundaryWord_all

/-- Clause (a) for the odd standard tile of every word. -/
theorem clauseA_standard_odd_all (w : Word) :
    IsRegularAlmostTiling (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) :=
  clauseA_standard_odd_of_boundary standardBoundaryWord_all w

/-- Clause (a) for the even standard tile of every word. -/
theorem clauseA_standard_even_all (w : Word) :
    IsRegularAlmostTiling (cellTileOf (evenTile w)) (texV1Even (fracEven w)) (texV2 (fracEven w)) :=
  clauseA_standard_even_of_boundary standardBoundaryWord_all w

/-- The edge-sharing clause for the odd standard tile of every word. -/
theorem edgeClauseA_odd_all (w : Word) :
    EdgeSharingClause (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) :=
  edgeClauseA_odd standardInputsAll w

/-- The odd standard tile covers its modified deck, for every word. -/
theorem deck_covers_odd_all (w : Word) : (fracOdd w).modifiedDeck.Covers (oddTile w) :=
  deck_covers_odd (fun v => (standardBoundaryWord_all v).1) simpleOdd_all w

/-- The even standard tile covers its modified deck, for every word. -/
theorem deck_covers_even_all (w : Word) : (fracEven w).modifiedDeck.Covers (evenTile w) :=
  deck_covers_even (fun v => (standardBoundaryWord_all v).2) simpleEven_all w

/-- Any site set equal to the odd standard tile covers its modified deck, for every word. -/
theorem covers_of_eq_odd_all {P : Finset Site} {w : Word} (h : P = oddTile w) :
    (fracOdd w).modifiedDeck.Covers P :=
  covers_of_eq_odd (fun v => (standardBoundaryWord_all v).1) simpleOdd_all h

/-- Any site set equal to the even standard tile covers its modified deck, for every word. -/
theorem covers_of_eq_even_all {P : Finset Site} {w : Word} (h : P = evenTile w) :
    (fracEven w).modifiedDeck.Covers P :=
  covers_of_eq_even (fun v => (standardBoundaryWord_all v).2) simpleEven_all h

/-- **Boundary tiling, odd tile, for every word (2723 part 2).** The boundary word `w1 w2 hat(rev w1) hat(rev w2)` of the cell
tile, the hypotheses of `almost_square_tiling` for `w1 = oddBottom w`, `w2 = oddRight w`, and the two sums. -/
theorem boundaryTilingOdd_all (w : Word) :
    StandardBoundaryOdd w ∧ IsSimpleTile (cellTileOf (oddTile w)) ∧
      (Admissible (oddBottom w) ∧ Admissible ((oddRight w).map Unit4.mulNegI)) ∧
      (NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
        NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w))) ∧
      almostV₁ (oddBottom w) = texV1Odd (fracOdd w) ∧ almostV₂ (oddRight w) = texV2 (fracOdd w) :=
  ⟨(standardBoundaryWord_all w).1, simpleOdd_all w, StandardBoundary.admissible_oddStandard w, packOdd_all w,
    StandardBoundary.sum_oddBottom w, StandardBoundary.sum_oddRight w⟩

/-- **Boundary tiling, even tile, for every word (2723 part 2).** -/
theorem boundaryTilingEven_all (w : Word) :
    StandardBoundaryEven w ∧ IsSimpleTile (cellTileOf (evenTile w)) ∧
      (Admissible (evenBottom w) ∧ Admissible ((evenRight w).map Unit4.mulNegI)) ∧
      (NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
        NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w))) ∧
      almostV₁ (evenBottom w) = texV1Even (fracEven w) ∧ almostV₂ (evenRight w) = texV2 (fracEven w) :=
  ⟨(standardBoundaryWord_all w).2, simpleEven_all w, StandardBoundary.admissible_evenStandard w, packEven_all w,
    StandardBoundary.sum_evenBottom w, StandardBoundary.sum_evenRight w⟩

end FLatticePaper.Tiles.StandardAll
