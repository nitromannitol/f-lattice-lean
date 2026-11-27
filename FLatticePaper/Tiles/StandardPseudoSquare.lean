import FLatticePaper.Tiles.PseudoSquare
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.VerticalRight
import FLatticePaper.Tiles.StandardAll

/-! The trace identities of the standard tiles (lemma:pseudo-square-boundary-word, Table 1).

`IsPseudoSquare T wh wv` carries the traces `lo = G(wh)` and `ri = G(wv)` as fields. For the standard tiles these are not
hypotheses: the bottom edges are `G` of the horizontal child words (`RegisterLink.oddBottom_eq_gH`,
`RegisterLink.evenBottom_eq_gH`), the right edges are `G` of the vertical child words (`VerticalRight.oddRight_eq_gV`,
`VerticalRight.evenRight_eq_gV`), and the boundary words are those of `StandardAll.boundaryTilingOdd_all` and
`boundaryTilingEven_all`. So each standard tile is a `(hWordOf w _, vWordOf w _)`-pseudo-square, and the conclusions of
`pseudoSquare_boundaryWord`, `pseudoSquare_halfTurn` and `pseudoSquare_quarterTurn` hold for it. -/

namespace FLatticePaper.Tiles.StandardPseudoSquare

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.StandardAll

/-- The odd standard tile of `w` is a `(hWordOf w false, vWordOf w false)`-pseudo-square. -/
theorem isPseudoSquare_odd (w : Word) :
    IsPseudoSquare (cellTileOf (oddTile w)) (hWordOf w false) (vWordOf w false) :=
  ⟨⟨(0, 0), oddBottom w, oddRight w, (boundaryTilingOdd_all w).1, RegisterLink.oddBottom_eq_gH w,
    VerticalRight.oddRight_eq_gV w⟩⟩

/-- The even standard tile of `w` is a `(hWordOf w true, vWordOf w true)`-pseudo-square. -/
theorem isPseudoSquare_even (w : Word) :
    IsPseudoSquare (cellTileOf (evenTile w)) (hWordOf w true) (vWordOf w true) :=
  ⟨⟨(0, 0), evenBottom w, evenRight w, (boundaryTilingEven_all w).1, RegisterLink.evenBottom_eq_gH w,
    VerticalRight.evenRight_eq_gV w⟩⟩

/-- The boundary word of the odd standard tile is `G(w_h, w_v)` in the four-part form. -/
theorem odd_boundaryWord (w : Word) :
    IsBoundaryWord (cellTileOf (oddTile w))
      (pseudoBoundaryWord (gH (hWordOf w false)) (gV (vWordOf w false))) :=
  pseudoSquare_boundaryWord (isPseudoSquare_odd w)

/-- The boundary word of the even standard tile is `G(w_h, w_v)` in the four-part form. -/
theorem even_boundaryWord (w : Word) :
    IsBoundaryWord (cellTileOf (evenTile w))
      (pseudoBoundaryWord (gH (hWordOf w true)) (gV (vWordOf w true))) :=
  pseudoSquare_boundaryWord (isPseudoSquare_even w)

/-- The 180-degree symmetry of the odd standard tile's boundary word. -/
theorem odd_halfTurn (w : Word) :
    IsBoundaryWord (cellTileOf (oddTile w))
        (pseudoBoundaryWord (gH (hWordOf w false)) (gV (vWordOf w false))) ∧
      (pseudoBoundaryWord (gH (hWordOf w false)) (gV (vWordOf w false))).map Unit4.neg =
        (pseudoBoundaryWord (gH (hWordOf w false)) (gV (vWordOf w false))).rotate
          ((gH (hWordOf w false)).length + (gV (vWordOf w false)).length) :=
  pseudoSquare_halfTurn (isPseudoSquare_odd w)

/-- The 180-degree symmetry of the even standard tile's boundary word. -/
theorem even_halfTurn (w : Word) :
    IsBoundaryWord (cellTileOf (evenTile w))
        (pseudoBoundaryWord (gH (hWordOf w true)) (gV (vWordOf w true))) ∧
      (pseudoBoundaryWord (gH (hWordOf w true)) (gV (vWordOf w true))).map Unit4.neg =
        (pseudoBoundaryWord (gH (hWordOf w true)) (gV (vWordOf w true))).rotate
          ((gH (hWordOf w true)).length + (gV (vWordOf w true)).length) :=
  pseudoSquare_halfTurn (isPseudoSquare_even w)

/-- The quarter turn of the odd standard tile's boundary word: the rotated pair `(F(w_v), F(w_h))` gives the rotated word. -/
theorem odd_quarterTurn (w : Word) :
    pseudoBoundaryWord (gPseudo (rotPseudo (hWordOf w false) (vWordOf w false)).1
        (rotPseudo (hWordOf w false) (vWordOf w false)).2).1
      (gPseudo (rotPseudo (hWordOf w false) (vWordOf w false)).1
        (rotPseudo (hWordOf w false) (vWordOf w false)).2).2 =
      ((pseudoBoundaryWord (gH (hWordOf w false)) (gV (vWordOf w false))).map Unit4.mulI).rotate
        ((gH (hWordOf w false)).length + (gV (vWordOf w false)).length + (gH (hWordOf w false)).length) :=
  pseudoSquare_quarterTurn (hWordOf w false) (vWordOf w false)

/-- The quarter turn of the even standard tile's boundary word. -/
theorem even_quarterTurn (w : Word) :
    pseudoBoundaryWord (gPseudo (rotPseudo (hWordOf w true) (vWordOf w true)).1
        (rotPseudo (hWordOf w true) (vWordOf w true)).2).1
      (gPseudo (rotPseudo (hWordOf w true) (vWordOf w true)).1
        (rotPseudo (hWordOf w true) (vWordOf w true)).2).2 =
      ((pseudoBoundaryWord (gH (hWordOf w true)) (gV (vWordOf w true))).map Unit4.mulI).rotate
        ((gH (hWordOf w true)).length + (gV (vWordOf w true)).length + (gH (hWordOf w true)).length) :=
  pseudoSquare_quarterTurn (hWordOf w true) (vWordOf w true)

end FLatticePaper.Tiles.StandardPseudoSquare
