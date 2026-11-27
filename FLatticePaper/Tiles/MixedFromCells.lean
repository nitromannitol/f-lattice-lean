import FLatticePaper.Tiles.CellRegisters
import FLatticePaper.Tiles.H2OddMarks
import FLatticePaper.Tiles.H2EvenMarks

/-! The mixed-piece claim of the odd child from the cell facts. The two walk forms of H2 for the standard tiles
(`H2OddMarks.H2o_odd_full`, `H2EvenMarks.H2e_even_full`) supply the inputs `H2o`, `H2e` of `CellRegisters.mixedOdd_of_cells`; the
only remaining input is the copy-level disjointness `H3`, taken as a named hypothesis. -/

namespace FLatticePaper.Tiles.MixedFromCells

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CellRegisters FLatticePaper.Tiles.MixedPieces

/-- **The mixed-piece claim of the odd child**, with the walk forms of H2 for both standard tiles and the named input `H3`. -/
theorem mixedOdd_full (w : Word) (H3 : CellsDisjointOdd w) : MixedPiecesInMarksOdd w :=
  mixedOdd_of_cells w (fun u => H2OddMarks.H2o_odd_full u) (fun u => H2EvenMarks.H2e_even_full u) H3

end FLatticePaper.Tiles.MixedFromCells
