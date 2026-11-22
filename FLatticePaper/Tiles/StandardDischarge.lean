import FLatticePaper.Tiles.StandardSimple
import FLatticePaper.Tiles.DeckCoverage

/-! Task 53, discharge. The simplicity inputs `simpleOdd`, `simpleEven` of clause (a) and of deck coverage are no longer
inputs: they follow from the boundary-word statement `StandardBoundaryWord` (`StandardSimple`). The remaining inputs are
the boundary-word statement and the packing hypotheses (`NoFirstCrossing`, `NoFarAdjacency`), which are not part of this
task. -/

namespace FLatticePaper.Tiles.StandardDischarge

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardSimple
open FLatticePaper.Tiles.DeckCoverage

/-- The standard inputs of clause (a) with the simplicity discharged: only the boundary-word statement and the packing
inputs remain. -/
def standardInputsDischarged (bd : ∀ w, StandardBoundaryWord w)
    (packO : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)))
    (packE : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w))) :
    StandardInputs :=
  standardInputsOf bd (simpleOdd_of_standardBoundaryWord bd) (simpleEven_of_standardBoundaryWord bd) packO packE

/-- Clause (a) for the odd tile of every word, from the boundary-word statement and the packing inputs only. -/
theorem clauseA_standard_odd_discharged (bd : ∀ w, StandardBoundaryWord w)
    (packO : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)))
    (packE : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)))
    (w : Word) :
    IsRegularAlmostTiling (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) :=
  clauseA_odd (standardInputsDischarged bd packO packE) w

/-- Clause (a) for the even tile of every word, from the boundary-word statement and the packing inputs only. -/
theorem clauseA_standard_even_discharged (bd : ∀ w, StandardBoundaryWord w)
    (packO : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)))
    (packE : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)))
    (w : Word) :
    IsRegularAlmostTiling (cellTileOf (evenTile w)) (texV1Even (fracEven w)) (texV2 (fracEven w)) :=
  clauseA_even (standardInputsDischarged bd packO packE) w

/-- The odd standard tile covers its modified deck, from the boundary-word statement alone. -/
theorem deck_covers_odd_discharged (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    (fracOdd w).modifiedDeck.Covers (oddTile w) :=
  deck_covers_odd (fun v => (bd v).1) (simpleOdd_of_standardBoundaryWord bd) w

/-- The even standard tile covers its modified deck, from the boundary-word statement alone. -/
theorem deck_covers_even_discharged (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    (fracEven w).modifiedDeck.Covers (evenTile w) :=
  deck_covers_even (fun v => (bd v).2) (simpleEven_of_standardBoundaryWord bd) w

/-- Any site set equal to the odd standard tile covers its modified deck, from the boundary-word statement alone. -/
theorem covers_of_eq_odd_discharged (bd : ∀ w, StandardBoundaryWord w) {P : Finset Site} {w : Word}
    (h : P = oddTile w) : (fracOdd w).modifiedDeck.Covers P :=
  covers_of_eq_odd (fun v => (bd v).1) (simpleOdd_of_standardBoundaryWord bd) h

/-- Any site set equal to the even standard tile covers its modified deck, from the boundary-word statement alone. -/
theorem covers_of_eq_even_discharged (bd : ∀ w, StandardBoundaryWord w) {P : Finset Site} {w : Word}
    (h : P = evenTile w) : (fracEven w).modifiedDeck.Covers P :=
  covers_of_eq_even (fun v => (bd v).2) (simpleEven_of_standardBoundaryWord bd) h

end FLatticePaper.Tiles.StandardDischarge
