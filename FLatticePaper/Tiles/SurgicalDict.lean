import FLatticePaper.Tiles.StandardTiles

/-! # Placed copies of standard and alternate tiles (surgical edition, Section 7 notation; for Section 8)

Section 7 writes the pieces of a standard or alternate decomposition as copies of a tile `T(p_1)`, `T(q_1)` or `T^{ds}(·)`,
with superscripts `±` and an index `1, 2` for doubled copies. These are placed by printed offsets. This file gives those
copies as Lean functions of the tiles and of the generator vectors (parameters), so that they can be used for any standard
tiles, not only the tiles of one word. Nothing here is a subtile of a stacked string: the superscripts `T^{±,i}` of the
zero-one strings (Section 5) are a different object and are not defined here.

* doubling (`eq:doubled_tiles`, `eq:alt_doubled`): `T ∪ (T + v)`;
* standard decompositions (`eq:standard_decompositions`) with the offsets of `eq:offsets_w1_odd` and `eq:offsets_w1_even`;
* alternate decompositions (`eq:alt_decomp`) with the offsets of `eq:alt_offsets_w1_odd` and `eq:alt_offsets_w1_even`, the
  alternate piece `T̂(q_1)` (or `T̂(p_1)`) being placed at the offset supplied by the caller (the type-dependent offsets of the
  text are a separate input).

Vectors are `v_{p_1,1}`, `v_{p_1,2}`, `v_{q_1,1}`, `v_{q_1,2}` (parameters `vp1 vp2 vq1 vq2`). -/

namespace FLatticePaper.Tiles.SurgicalDict

open FLatticePaper.Tiles.Standard

/-- `T ∪ (T + v)`: the doubled tile of `eq:doubled_tiles` and `eq:alt_doubled`. -/
def doubled (T : Tile) (v : Site) : Tile := T ∪ shift T v

/-- The pieces of `T(p_0)` in `eq:standard_decompositions`: `T(p_1)^+`, `T(p_1)^-`, `T^d(q_1)^+`, `T^d(q_1)^-`. -/
inductive P0Piece
  | p1Plus
  | p1Minus
  | q1DPlus
  | q1DMinus
  deriving DecidableEq, Repr

/-- The pieces of `T(q_0)` in `eq:standard_decompositions`: `T^d(p_1)^+`, `T^d(p_1)^-`, `T(q_1)^+`, `T(q_1)^-`. -/
inductive Q0Piece
  | p1DPlus
  | p1DMinus
  | q1Plus
  | q1Minus
  deriving DecidableEq, Repr

/-- `c(T) − c(T(p_0))` of `eq:offsets_w1_odd` (`odd = true`) and `eq:offsets_w1_even` (`odd = false`). -/
def offsetP0 (odd : Bool) (vp1 vp2 vq1 vq2 : Site) : P0Piece → Site
  | .p1Plus => if odd then 0 else vq1 + vq1
  | .p1Minus => if odd then vq1 + vq1 + vq2 else vq2
  | .q1DPlus => if odd then vp1 else 0
  | .q1DMinus => if odd then vp2 else vp1 + vp2

/-- `c(T) − c(T(q_0))` of `eq:offsets_w1_odd` and `eq:offsets_w1_even`. -/
def offsetQ0 (odd : Bool) (vp1 vp2 vq1 vq2 : Site) : Q0Piece → Site
  | .p1DPlus => if odd then 0 else vq1
  | .p1DMinus => if odd then vq1 + vq2 else vq1
  | .q1Plus => if odd then vp1 else 0
  | .q1Minus => if odd then vp2 + vp2 else vp1 + vp2 + vp2

/-- The tile of a piece of `T(p_0)`: `T(p_1)` (plain) or `T^d(q_1)` (doubled with `v_{q_1,1}`). -/
def placeP0 (odd : Bool) (Tp Tq : Tile) (vp1 vp2 vq1 vq2 : Site) (x : P0Piece) : Tile :=
  match x with
  | .p1Plus => shift Tp (offsetP0 odd vp1 vp2 vq1 vq2 .p1Plus)
  | .p1Minus => shift Tp (offsetP0 odd vp1 vp2 vq1 vq2 .p1Minus)
  | .q1DPlus => shift (doubled Tq vq1) (offsetP0 odd vp1 vp2 vq1 vq2 .q1DPlus)
  | .q1DMinus => shift (doubled Tq vq1) (offsetP0 odd vp1 vp2 vq1 vq2 .q1DMinus)

/-- The tile of a piece of `T(q_0)`: `T^d(p_1)` (doubled with `v_{p_1,2}`) or `T(q_1)` (plain). -/
def placeQ0 (odd : Bool) (Tp Tq : Tile) (vp1 vp2 vq1 vq2 : Site) (x : Q0Piece) : Tile :=
  match x with
  | .p1DPlus => shift (doubled Tp vp2) (offsetQ0 odd vp1 vp2 vq1 vq2 .p1DPlus)
  | .p1DMinus => shift (doubled Tp vp2) (offsetQ0 odd vp1 vp2 vq1 vq2 .p1DMinus)
  | .q1Plus => shift Tq (offsetQ0 odd vp1 vp2 vq1 vq2 .q1Plus)
  | .q1Minus => shift Tq (offsetQ0 odd vp1 vp2 vq1 vq2 .q1Minus)

/-- The pieces of an alternate decomposition of `T̂(p_0)` (`eq:alt_decomp`) besides `T̂(q_1)`: `T^{ds}(p_1)^±` and
`T(q_1)^±`. `Sp`, `Sq` are the doubling shifts of `eq:alt_doubled`. -/
inductive AltP0Piece
  | dsP1Plus
  | dsP1Minus
  | q1Plus
  | q1Minus
  deriving DecidableEq, Repr

/-- `c(T) − c(T̂(p_0))` for the pieces of `eq:alt_offsets_w1_odd` (`odd = true`) and `eq:alt_offsets_w1_even`. -/
def altOffsetP0 (odd : Bool) (vp1 vp2 vq1 vq2 : Site) : AltP0Piece → Site
  | .q1Plus => if odd then vp1 else 0
  | .q1Minus => if odd then vp2 + vp2 - vq1 else vp1 + vp2 + vp2 + vq1
  | .dsP1Plus => if odd then 0 else vq1
  | .dsP1Minus => if odd then vq1 + vq2 else vq2

/-- The alternate pieces of `T̂(p_0)`: `T^{ds}(p_1)^±` doubled with the shift `Sp`, and `T(q_1)^±`. -/
def placeAltP0 (odd : Bool) (Tp Tq : Tile) (Sp : Site) (vp1 vp2 vq1 vq2 : Site) (x : AltP0Piece) : Tile :=
  match x with
  | .dsP1Plus => shift (doubled Tp Sp) (altOffsetP0 odd vp1 vp2 vq1 vq2 .dsP1Plus)
  | .dsP1Minus => shift (doubled Tp Sp) (altOffsetP0 odd vp1 vp2 vq1 vq2 .dsP1Minus)
  | .q1Plus => shift Tq (altOffsetP0 odd vp1 vp2 vq1 vq2 .q1Plus)
  | .q1Minus => shift Tq (altOffsetP0 odd vp1 vp2 vq1 vq2 .q1Minus)

/-- The alternate pieces of `T̂(q_0)` (`eq:alt_decomp`): `T(p_1)^±` and `T^{ds}(q_1)^±` doubled with `Sq`. -/
inductive AltQ0Piece
  | p1Plus
  | p1Minus
  | dsQ1Plus
  | dsQ1Minus
  deriving DecidableEq, Repr

/-- `c(T) − c(T̂(q_0))` for the pieces of `eq:alt_offsets_w1_odd` and `eq:alt_offsets_w1_even`. -/
def altOffsetQ0 (odd : Bool) (vp1 vp2 vq1 vq2 : Site) : AltQ0Piece → Site
  | .dsQ1Plus => if odd then vp1 else 0
  | .dsQ1Minus => if odd then vp2 else vp1 + vp2
  | .p1Plus => if odd then 0 else vq1
  | .p1Minus => if odd then vp2 + vq2 + vq1 + vq1 else vp2 + vq2 - vq1

/-- The alternate pieces of `T̂(q_0)`: `T(p_1)^±` and `T^{ds}(q_1)^±` (doubled with `Sq`). -/
def placeAltQ0 (odd : Bool) (Tp Tq : Tile) (Sq : Site) (vp1 vp2 vq1 vq2 : Site) (x : AltQ0Piece) : Tile :=
  match x with
  | .dsQ1Plus => shift (doubled Tq Sq) (altOffsetQ0 odd vp1 vp2 vq1 vq2 .dsQ1Plus)
  | .dsQ1Minus => shift (doubled Tq Sq) (altOffsetQ0 odd vp1 vp2 vq1 vq2 .dsQ1Minus)
  | .p1Plus => shift Tp (altOffsetQ0 odd vp1 vp2 vq1 vq2 .p1Plus)
  | .p1Minus => shift Tp (altOffsetQ0 odd vp1 vp2 vq1 vq2 .p1Minus)

end FLatticePaper.Tiles.SurgicalDict
