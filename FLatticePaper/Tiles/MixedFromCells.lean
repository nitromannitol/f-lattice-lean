import FLatticePaper.Tiles.CellRegisters
import FLatticePaper.Tiles.H2OddMarks
import FLatticePaper.Tiles.H2EvenMarks
import FLatticePaper.Tiles.H3Pairs

/-! The mixed-piece claim of the odd child from the cell facts. The two walk forms of H2 for the standard tiles
(`H2OddMarks.H2o_odd_full`, `H2EvenMarks.H2e_even_full`) supply the inputs `H2o`, `H2e` of `CellRegisters.mixedOdd_of_cells`; the
only remaining input is the copy-level disjointness `H3`, taken as a named hypothesis. -/

namespace FLatticePaper.Tiles.MixedFromCells

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CellRegisters FLatticePaper.Tiles.MixedPieces
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteInduction

/-- **The mixed-piece claim of the odd child**, with the walk forms of H2 for both standard tiles and the named input `H3`. -/
theorem mixedOdd_full (w : Word) (H3 : CellsDisjointOdd w) : MixedPiecesInMarksOdd w :=
  mixedOdd_of_cells w (fun u => H2OddMarks.H2o_odd_full u) (fun u => H2EvenMarks.H2e_even_full u) H3

/-- **The mixed-piece claim of the even child**, with the walk forms of H2 for both standard tiles and the named input `H3`. -/
theorem mixedEven_full (w : Word) (H3 : H3Pairs.CellsDisjointEven w) : MixedPiecesInMarksEven w := by
  unfold MixedPiecesInMarksEven
  intro u1 u2 hT1 hT2 a ha b hb z h1 h2
  exact mixed_copies_of_cells (oddTile u1) (evenTile u2) (marksOdd u1) (marksEven u2) a b
    (tileH1_of_hcc _ (oddTile_hcc u1)) (tileH1_of_hcc _ (evenTile_hcc u2))
    (H2OddMarks.H2o_odd_full u1) (H2EvenMarks.H2e_even_full u2) (H3 u1 u2 hT1 hT2 a ha b hb) z h1 h2

/-- **The mixed-piece claim of the odd child for a non-base word**, with `H3` discharged by `H3Pairs.cellsDisjointOdd`. -/
theorem mixedOdd_all (w : Word) (hw : ¬ IsBase w) : MixedPiecesInMarksOdd w :=
  mixedOdd_full w (H3Pairs.cellsDisjointOdd w hw)

/-- **The mixed-piece claim of the even child for a non-base word**, with `H3` discharged by `H3Pairs.cellsDisjointEven`. -/
theorem mixedEven_all (w : Word) (hw : ¬ IsBase w) : MixedPiecesInMarksEven w :=
  mixedEven_full w (H3Pairs.cellsDisjointEven w hw)

end FLatticePaper.Tiles.MixedFromCells
