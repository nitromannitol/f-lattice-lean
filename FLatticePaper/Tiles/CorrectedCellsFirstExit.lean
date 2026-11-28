import FLatticePaper.Tiles.CorrectedCellsOrdinary

/-! The corrected domain clauses at the first pure-two and pure-three exits.
These are the first corrections using the enlarged one-tile and the translated bridge. -/

namespace FLatticePaper.Tiles.CorrectedCellsFirstExit

open FLatticePaper.Farey FLatticePaper.Tiles JointFamily Standard LCorrecProps

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)
private abbrev LO (w : Word) (s e : Bool) := domOdo (oddLCells w s e)
private abbrev LE (w : Word) (s e : Bool) := domOdo (evenLCells w s e)

set_option maxRecDepth 8192
set_option maxHeartbeats 400000

/-- The ordinary even L gives exactly the odd standard tile at the first pure-two exit. -/
theorem odd_two_three : pieceUnion (tileOddPieces cellData O E LE [.two,.three]) = oddTile [.two,.three] := by
  decide +kernel

/-- The elongated even L gives the even alternate tile at the same exit. -/
theorem alt_even_two_three :
    pieceUnion (tileAltEvenPieces cellData O E AO AE LE [.two,.three]) = altEvenT [.two,.three] := by
  decide +kernel

/-- With the translated bridge, the ordinary odd L gives the even standard tile at the first pure-three exit. -/
theorem even_three_two : pieceUnion (tileEvenPieces cellData O E LO [.three,.two]) = evenTile [.three,.two] := by
  decide +kernel

/-- The elongated odd L gives the odd alternate tile at the same exit. -/
theorem alt_odd_three_two :
    pieceUnion (tileAltOddPieces cellData O E AO AE LO [.three,.two]) = altOddT [.three,.two] := by
  decide +kernel

end FLatticePaper.Tiles.CorrectedCellsFirstExit
