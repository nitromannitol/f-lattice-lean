import FLatticePaper.Tiles.CornerPositions
import FLatticePaper.Tiles.StandardAll

/-! The register corner positions in the offset form: `almostV₁ (bottom word) = texV1 (fraction)` (`boundaryTilingOdd_all`,
`boundaryTilingEven_all`), so the last position of the forward tile list of a register is `texV1 (fraction) - (1,1)`, the offset
that the junction step of the piece placements requires. -/

namespace FLatticePaper.Tiles.TexVPositions

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause

theorem almostV1_oddBottom_eq (w : Word) : almostV₁ (oddBottom w) = texV1Odd (fracOdd w) :=
  (FLatticePaper.Tiles.StandardAll.boundaryTilingOdd_all w).2.2.2.2.1

theorem almostV1_evenBottom_eq (w : Word) : almostV₁ (evenBottom w) = texV1Even (fracEven w) :=
  (FLatticePaper.Tiles.StandardAll.boundaryTilingEven_all w).2.2.2.2.1

theorem lastPos_hWordOf_false_tex (w : Word) :
    lastPosOf (hStringAt (hWordOf w false) (0, 0)) = texV1Odd (fracOdd w) - (1, 1) := by
  rw [FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_false, almostV1_oddBottom_eq]

theorem lastPos_hWordOf_true_tex (w : Word) :
    lastPosOf (hStringAt (hWordOf w true) (0, 0)) = texV1Even (fracEven w) - (1, 1) := by
  rw [FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_true, almostV1_evenBottom_eq]

end FLatticePaper.Tiles.TexVPositions
