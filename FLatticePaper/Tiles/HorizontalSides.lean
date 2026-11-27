import FLatticePaper.Tiles.HBottom
import FLatticePaper.Tiles.StringCover
import FLatticePaper.Tiles.StandardBoundary

/-! The bottom side of a standard tile is covered by its horizontal string (S2 of the overlap form of H2): every point of the walk
of the bottom edge lies in the string sites (`HBottom.hB_odd`, `HBottom.hB_even`), hence in the tile covers of the string
(`StringCover.covers_iff_stringSites`). -/

namespace FLatticePaper.Tiles.HorizontalSides

open FLatticePaper.Tiles FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.StandardBoundary

/-- **S2, odd child.** The bottom walk of the odd tile is covered by the horizontal string of its word. -/
theorem bottom_covered_odd (w : Word) :
    ∀ z ∈ F2Word.walk 0 (oddBottom w), tileCovers (hStringAt (hWordOf w false) 0) z :=
  fun z hz => (FLatticePaper.Tiles.StringCover.covers_iff_stringSites (hWordOf w false) z).2
    (FLatticePaper.Tiles.HBottom.hB_odd w z hz)

/-- **S2, even child.** The bottom walk of the even tile is covered by the horizontal string of its word. -/
theorem bottom_covered_even (w : Word) :
    ∀ z ∈ F2Word.walk 0 (evenBottom w), tileCovers (hStringAt (hWordOf w true) 0) z :=
  fun z hz => (FLatticePaper.Tiles.StringCover.covers_iff_stringSites (hWordOf w true) z).2
    (FLatticePaper.Tiles.HBottom.hB_even w z hz)

end FLatticePaper.Tiles.HorizontalSides
