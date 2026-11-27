import FLatticePaper.Tiles.PseudoSquareSites
import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! # Partial tiles and doubled tiles (surgical edition, `def:partial_tile` and `def:standard_odometer_doubling`)

A pseudo-square `T` with strings `(w_h, w_v)` has its four zero-one strings placed at its lower-left vertex `c(T)`
(`pseudoStrings`, the clauses of `def:tile_boundary_strings`). A partial tile `T^{h±/v±}` is a tile that contains the string
of one side of `T`: the case set of `def:partial_tile` gives the four side strings `w_h`, `rev w_h`, `w_v`, `rev w_v`.
A boundary tile contains all four strings. The doubled tile of `def:standard_odometer_doubling` is the union of the
boundary tile and the partial tile translated by `v_{n/d}`.

A tile is a `CellTile` (a finite set of cells, identified by lower-left corners) with `IsSimpleTile`, the Section 4
predicate (`Tiles/AlmostTiling.lean`). Its point set is its vertex set `CellTile.vertices`; the side strings are point sets
(`placedSites`, from `tileShape`), and all containments are between point sets (operator convention, af007b5). -/

namespace FLatticePaper.Tiles

/-- The four sides of a partial tile: `h^+`, `h^-`, `v^+`, `v^-`. -/
inductive Side
  | hPlus
  | hMinus
  | vPlus
  | vMinus
  deriving DecidableEq, Repr

/-- The zero-one string of one side of a pseudo-square with words `(w_h, w_v)` and lower-left vertex `c`:
`w_h` (case `h^+`), `rev w_h` (case `h^-`), `w_v` (case `v^+`), `rev w_v` (case `v^-`), with the E07 anchors of
`anchoredStrings`: the forward horizontal string at `c`, the reversed vertical string at `c`, the forward vertical string
at the last position of the forward horizontal string, and the reversed horizontal string at the last position of the
reversed vertical string. -/
def sideString (wh wv : BinaryWord) (c : GInt) : Side → List (ZTile × GInt)
  | .hPlus => hStringAt wh c
  | .hMinus => hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse c))
  | .vPlus => vStringAt wv (lastPosOf (hStringAt wh c))
  | .vMinus => vRevStringAt wv.reverse c

/-- The sites of the side string of `T` (with lower-left vertex `c(T)`), or none when `T` is empty. -/
noncomputable def sidePlaced (wh wv : BinaryWord) (T : CellTile) (s : Side) : List GInt :=
  match lowerLeftList T.vertices.toList with
  | none => []
  | some c => placedSites (sideString wh wv c s)

/-- `T'` is a partial tile of `T` on side `s` (`def:partial_tile`): `T'` is a tile (`IsSimpleTile`, Section 4) and
`T' ∩ T` contains the side string of `T` on `s` (the case set `T^{h±/v±} ∩ T ⊃ …`). -/
def IsPartialTile (T' T : CellTile) (wh wv : BinaryWord) (s : Side) : Prop :=
  IsSimpleTile T' ∧ ∀ x ∈ sidePlaced wh wv T s, x ∈ T'.vertices ∧ x ∈ T.vertices

/-- `T'` is a boundary tile of `T`: it contains the four side strings of `T` (`T^b ∩ T ⊃ w_h ∪ rev w_h ∪ w_v ∪ rev w_v`). -/
def IsBoundaryTile (T' T : CellTile) (wh wv : BinaryWord) : Prop :=
  IsSimpleTile T' ∧ ∀ s : Side, ∀ x ∈ sidePlaced wh wv T s, x ∈ T'.vertices ∧ x ∈ T.vertices

/-- The doubled tile `T^{d,p,±} = T^b ∪ (T^{h±/v±} + v)` of `def:standard_odometer_doubling` (as a set of cells). -/
def doubledTile (Tb Th : CellTile) (v : GInt) : CellTile :=
  Tb ∪ Th.image (· + v)

end FLatticePaper.Tiles
