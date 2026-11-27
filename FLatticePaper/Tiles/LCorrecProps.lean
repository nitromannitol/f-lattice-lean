import FLatticePaper.Tiles.JointGlue

/-! # `lemma:l_correc_properties` and the corrected tiles, at the level of cells

Surgical edition 274ad18. The L-corrections and the corrected decompositions of `JointFamily` are read here with the standard
tiles (`oddTile`, `evenTile`) and the alternate tiles (`SurgicalAltTiles.altOddTile`, `altEvenTile`, with the base alternates of
`prop:base_cases` placed with `c(T̂) = 0`, `paperAltBaseTiles`) as the domains of the parents. The statements are:

* `LCorrecRotation`: `lemma:l_correc_properties` (1), `R(T^{L,+}(q_0)) = T^{L,-}(R(q_0))`, `R^2(T^{L,+}(q_0)) = T^{L,-}(q_0)`,
  `R^3(T^{L,+}(q_0)) = T^{L,+}(R(q_0))` up to translation, with `+` and `-` flipped on the right of the first and third lines when
  `W_1` is odd (the fourth line is trivial);
* `LCorrecSides`: `lemma:l_correc_properties` (2), the elongated `T^{L,±}(q_0)` contains the printed two sides of `T(q_0)`;
  `LCellSides`: every L-correction contains the sides `paperLSides` of its child;
* `CorrectedCells`: the corrected decompositions (definition of tile odometers) are the printed tiles.

They hold numerically for every word of length at most 4 (rotation, 116 words of each kind) and 5 (sides, 179 words; corrected
decompositions, 116 corrected and 237 uncorrected children of each of the four kinds), scripts `tmp-w6/chk1c.py`, `chk3.py`,
`chk6.py` (a line-by-line port of these definitions). They are stated here and not proved. -/

namespace FLatticePaper.Tiles.LCorrecProps

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.Standard (IsBase swapW oddTile evenTile zeroTile oneTile rot shift Tile)

/-! ### The base alternate tiles as finite sets, with `c(T̂) = 0` -/

/-- A box containing the base alternate tiles. -/
def boxF (d : ℤ) : Finset Site := Finset.Icc (-3 * d) (3 * d) ×ˢ Finset.Icc (-3 * d) (3 * d)

/-- `T̂_{1/d}` of `lemma:basecase_3k_even_alt` (`paperStairAltTile d`), with `c(T̂_{1/d}) = (0, 0)` by the exception of the text. -/
def stairAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    (x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1) ∨
    (x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d) ∨
    (1 - d ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = -1) ∨ (4 - d ≤ x.1 ∧ x.1 ≤ 3 ∧ x.2 = d + 1) ∨
    (4 - 2 * d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d ∧ -d + 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2)

/-- `T̂_{1/d}` of `lemma:basecase_3k_odd_alt` (`paperLadderAltTile d`), in the paper's chart (lower-left vertex `(-1, -1)`). -/
def ladderAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    ((x = (-1, -1) ∨ x = (d, d + 2)) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1) ∨
      (1 - d ≤ x.1 ∧ x.1 ≤ 2 * d - 2 ∧ -1 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ -1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 1)) ∧
    ¬ ((d ≤ x.1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 ≤ -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ d + 2))

/-- `T̂_{p_1}` of `lemma:basecase_2k_odd_alt` (`paperNearStairAltTile d`), in the paper's chart. -/
def nearStairAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    (-1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d) ∨ (d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2) ∨
    (x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d) ∨
    (x.1 = -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ 2 * d) ∨ (x.1 = d + 1 ∧ d - 2 ≤ x.2 ∧ x.2 ≤ 2 * d - 3) ∨
    (0 ≤ x.1 ∧ x.1 ≤ d ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 3 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d - 1)

/-- `T̂_{q_1}` of `lemma:basecase_2k_even_alt` (`paperNearLadderAltTile d`), in the paper's chart. -/
def nearLadderAltF (d : ℤ) : Finset Site :=
  (boxF d).filter fun x =>
    ((x = (-2, 2 * d) ∨ x = (d + 1, d - 1)) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1) ∨
      (-2 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬ ((x.1 ≤ -1 ∧ x.2 ≤ d - 1) ∨ (d ≤ x.1 ∧ 2 * d ≤ x.2))

/-- The base alternate tiles of the base words, in the frames of `PaperAltBaseCond`: the near-one alternates read at
`x + (0, 1)`, the odd alternate of `3^k` at `x - (1, 1)`, and `T̂_{1/d}` as it is (`c(T̂_{1/d}) = (0, 0)`). -/
def paperAltBaseTiles (w : Word) : Tile × Tile :=
  if w = [] then (shift (nearStairAltF 3) (0, -1), stairAltF 3)
  else if w = List.replicate w.length Digit.three then
    (shift (ladderAltF (2 * (w.length : ℤ) + 2)) (1, 1), stairAltF (2 * (w.length : ℤ) + 3))
  else (shift (nearStairAltF (2 * (w.length : ℤ) + 3)) (0, -1), shift (nearLadderAltF (2 * (w.length : ℤ) + 2)) (0, -1))

/-- The alternate tiles of the words, from the paper's base alternates. -/
def altOddT (w : Word) : Tile := SurgicalAltTiles.altOddTile paperAltBaseTiles w

/-- The even alternate tile of `w`. -/
def altEvenT (w : Word) : Tile := SurgicalAltTiles.altEvenTile paperAltBaseTiles w

/-! ### The cells of the L-corrections and of the corrected decompositions -/

/-- A partial odometer that only carries a domain. -/
def domOdo (T : Finset Site) : PartialOdometer := ⟨T, fun _ => 0⟩

/-- The register data of the cells: the initial tiles `T_{0/1}`, `T_{1/1}`. -/
def cellData : WeakData :=
  { zeroO := domOdo zeroTile, oneO := domOdo oneTile, bdry := fun _ _ => ∅, partialT := fun _ _ _ => ∅,
    base := fun _ _ _ => True }

/-- The cells of the odd L-correction `T^{L,±}(p_0)` of the odd child of `w`, in the frame of that child. -/
def oddLCells (w : Word) (plus elong : Bool) : Finset Site :=
  pieceUnion (oddLPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
    (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u)) w plus elong)

/-- The cells of the even L-correction `T^{L,±}(q_0)` of the even child of `w`, in the frame of that child. -/
def evenLCells (w : Word) (plus elong : Bool) : Finset Site :=
  pieceUnion (evenLPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
    (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u)) w plus elong)

/-- `lemma:l_correc_properties` (1), at the level of cells, up to translation. -/
def LCorrecRotation : Prop :=
  ∀ w : Word, EvenLDefined w → ∀ elong : Bool,
    (∃ t : Site, rot (evenLCells w true elong) = shift (oddLCells (swapW w) (W1Odd w) elong) t) ∧
    (∃ t : Site, rot (rot (evenLCells w true elong)) = shift (evenLCells w false elong) t) ∧
    (∃ t : Site, rot (rot (rot (evenLCells w true elong))) = shift (oddLCells (swapW w) (!W1Odd w) elong) t)

/-- `lemma:l_correc_properties` (2), at the level of cells: the elongated `T^{L,±}(q_0)` and `T(q_0)` both contain the printed
sides of `T(q_0)` (the boundary strings anchored at `c(T(q_0)) = 0`). -/
def LCorrecSides : Prop :=
  ∀ w : Word, EvenLDefined w → ∀ plus : Bool, ∀ s ∈ printedEvenSides (W1Odd w) plus,
    ∀ x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 s), x ∈ evenLCells w plus true ∧ x ∈ evenTile w

/-- Every L-correction and its child contain the sides `paperLSides` of the child. -/
def LCellSides : Prop :=
  (∀ w : Word, OddLDefined w → ∀ plus elong : Bool, ∀ s ∈ paperLSides true (W1Odd w) plus elong,
    ∀ x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 s), x ∈ oddLCells w plus elong ∧ x ∈ oddTile w) ∧
  (∀ w : Word, EvenLDefined w → ∀ plus elong : Bool, ∀ s ∈ paperLSides false (W1Odd w) plus elong,
    ∀ x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 s), x ∈ evenLCells w plus elong ∧ x ∈ evenTile w)

/-- The corrected decompositions of the tile odometers cover exactly the printed tiles: for every word that is not a base word,
the union of the placed pieces of `tileOddPieces`, ..., with the L-corrections of the parents, is the standard (resp. alternate)
tile. -/
def CorrectedCells : Prop :=
  ∀ w : Word, ¬ IsBase w →
    pieceUnion (tileOddPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
        (fun u s e => domOdo (evenLCells u s e)) w) = oddTile w ∧
    pieceUnion (tileEvenPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
        (fun u s e => domOdo (oddLCells u s e)) w) = evenTile w ∧
    pieceUnion (tileAltOddPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
        (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u)) (fun u s e => domOdo (oddLCells u s e)) w) =
      altOddT w ∧
    pieceUnion (tileAltEvenPieces cellData (fun u => domOdo (oddTile u)) (fun u => domOdo (evenTile u))
        (fun u => domOdo (altOddT u)) (fun u => domOdo (altEvenT u)) (fun u s e => domOdo (evenLCells u s e)) w) =
      altEvenT w

end FLatticePaper.Tiles.LCorrecProps
