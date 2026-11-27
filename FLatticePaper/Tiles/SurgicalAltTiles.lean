import FLatticePaper.Tiles.SurgicalAltOdometers
import FLatticePaper.Tiles.SurgicalAltTileLemma

/-! # The alternate tiles of the surgical edition (`def:alternate_tiles`, `eq:alt_decomp`) as point sets

The alternate children of a word are unions of placed copies: the alternate decomposition (`eq:alt_decomp`) places the doubled
standard tiles `T^{ds}(p_1)^±` (doubling shift `S_p`, `altShifts`), the standard tiles `T(q_1)^±`, and the alternate parent
`T̂(q_1)` (resp. `T̂(p_1)`), at the offsets of the coefficient tables of `SurgicalAlt` (`altP0Coeff`, `altQ0Coeff`,
`altQ1Coeff`, `altP1Coeff`). The standard registers are the standard tiles of `stateAt pre`; the alternate registers are
carried as in the standard recursion (`stepState`). The base alternate tiles are a parameter `base` (their paper tiles are
bridged separately). The pieces are placed by `Standard.shift`, and the doubled pieces by `SurgicalDict.doubled`.

Items (1) and (2) are stated (not proved here; the covering of (2) is checked numerically in E32); items (4) and (5) are stated with the readings (b), (c) isolated, pending the operator. -/

namespace FLatticePaper.Tiles.SurgicalAltTiles

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.SurgicalAlt
open FLatticePaper.Tiles.Standard (stateAt zeroTile oneTile swapW TState)

open Classical

/-- The alternate odd child of the word `pre`: the doubled standard odd register `T^{ds}(p_1)^±` (shift `S_p`), the standard
even register `T(q_1)^±`, and the alternate parent `T̂(q_1)` (the alternate even register `aEven`) when the type is not `two`. -/
def altOddPieces (pre : Word) (aEven : Standard.Tile) : Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let Sp := (altShifts odd vp2 vq1).1
  let cof : AltP0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altP0Coeff odd x)
  Standard.shift (doubled s.tOdd Sp) (cof .dsP1Plus) ∪ Standard.shift (doubled s.tOdd Sp) (cof .dsP1Minus) ∪
    Standard.shift s.tEven (cof .q1Plus) ∪ Standard.shift s.tEven (cof .q1Minus) ∪
    (match altTypeOf pre with
      | none => ∅
      | some ty =>
        match altQ1Coeff odd ty with
        | none => ∅
        | some c => Standard.shift aEven (coeffOff vp1 vp2 vq1 vq2 c))

/-- The alternate even child of the word `pre`: the standard odd register `T(p_1)^±`, the doubled standard even register
`T^{ds}(q_1)^±` (shift `S_q`), and the alternate parent `T̂(p_1)` (the alternate odd register `aOdd`) when the type is not
`three`. -/
def altEvenPieces (pre : Word) (aOdd : Standard.Tile) : Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let Sq := (altShifts odd vp2 vq1).2
  let cof : AltQ0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altQ0Coeff odd x)
  Standard.shift s.tOdd (cof .p1Plus) ∪ Standard.shift s.tOdd (cof .p1Minus) ∪
    Standard.shift (doubled s.tEven Sq) (cof .dsQ1Plus) ∪ Standard.shift (doubled s.tEven Sq) (cof .dsQ1Minus) ∪
    (match altTypeOf pre with
      | none => ∅
      | some ty =>
        match altP1Coeff odd ty with
        | none => ∅
        | some c => Standard.shift aOdd (coeffOff vp1 vp2 vq1 vq2 c))

/-- The alternate children of the word `pre` with the alternate registers `r`: the base alternates for base words, the
alternate decompositions otherwise. -/
def altChild (base : Word → Standard.Tile × Standard.Tile) (pre : Word) (r : Standard.Tile × Standard.Tile) :
    Standard.Tile × Standard.Tile :=
  if FLatticePaper.Tiles.Standard.IsBase pre then base pre
  else (altOddPieces pre r.2, altEvenPieces pre r.1)

/-- One letter of the alternate recursion: the alternate registers receive the children as the standard ones do. -/
def altStep (base : Word → Standard.Tile × Standard.Tile) (pre : Word) (r : Standard.Tile × Standard.Tile)
    (d : Digit) : Standard.Tile × Standard.Tile :=
  let ch := altChild base pre r
  match d with
  | .one => (ch.1, ch.2)
  | .two => (ch.1, r.2)
  | .three => (r.1, ch.2)

/-- Reads the letters of a word after the prefix `pre` on the alternate registers. -/
def altRun (base : Word → Standard.Tile × Standard.Tile) (pre : Word) :
    Word → Standard.Tile × Standard.Tile → Standard.Tile × Standard.Tile
  | [], r => r
  | d :: rest, r => altRun base (pre ++ [d]) rest (altStep base pre r d)

/-- The alternate registers after reading a word (initially the standard initial tiles). -/
def altRegs (base : Word → Standard.Tile × Standard.Tile) (w : Word) : Standard.Tile × Standard.Tile :=
  altRun base [] w (zeroTile, oneTile)

/-- The alternate odd child `T̂(p_0)` of the word `w`. -/
def altOddTile (base : Word → Standard.Tile × Standard.Tile) (w : Word) : Standard.Tile :=
  (altChild base w (altRegs base w)).1

/-- The alternate even child `T̂(q_0)` of the word `w`. -/
def altEvenTile (base : Word → Standard.Tile × Standard.Tile) (w : Word) : Standard.Tile :=
  (altChild base w (altRegs base w)).2

/-! ### Item (1) of `lemma:alternate_tile_properties` (surgical 571253f, lines 3594-3599), stated, not proved.

Item (3) is proved for the anchors (`alt_item3a`, `alt_item3b` in `SurgicalAltTileLemma`). Item (1) is stated below. Item (2) is stated (AltItem2),
items (4), (5) are stated with the readings isolated. -/

/-- Item (2), covering: the translates of `T̂(n/d)` by the lattice `L'(n/d)` (`paperLattice n d`, checked against the text at
lines 169 and 405 of the manuscript 9a5b401) cover every point of Z^2. -/
def AltItem2Covers (T : Standard.Tile) (n d : ℤ) : Prop :=
  ∀ z : GInt, ∃ y ∈ T, ∃ v ∈ FLatticePaper.Tiles.paperLattice n d, z = y + v

/-- Item (2) for the alternate children of every word: the odd child covers under `L'` of its fraction, and so does the even
child under `L'` of its fraction. -/
def AltItem2 (base : Word → Standard.Tile × Standard.Tile) : Prop :=
  ∀ w : Word,
    AltItem2Covers (altOddTile base w) ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den ∧
    AltItem2Covers (altEvenTile base w) ((parentsAt w).current .even).num ((parentsAt w).current .even).den

/-! ### The subtiles of the alternate children (the pieces of `altOddPieces`, `altEvenPieces`) -/

/-- The subtiles of the alternate odd child of `pre` (`eq:alt_decomp`, first line): the four placed pieces and the parent
piece `T̂(q_1)` (when the type is not `two`). -/
def altOddSubtiles (pre : Word) (aEven : Standard.Tile) : List Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let Sp := (altShifts odd vp2 vq1).1
  let cof : AltP0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altP0Coeff odd x)
  [Standard.shift (doubled s.tOdd Sp) (cof .dsP1Plus), Standard.shift (doubled s.tOdd Sp) (cof .dsP1Minus),
    Standard.shift s.tEven (cof .q1Plus), Standard.shift s.tEven (cof .q1Minus)] ++
  (match altTypeOf pre with
    | none => []
    | some ty =>
      match altQ1Coeff odd ty with
      | none => []
      | some c => [Standard.shift aEven (coeffOff vp1 vp2 vq1 vq2 c)])

/-- The subtiles of the alternate even child of `pre`: the two standard odd pieces, the two doubled standard even pieces, and
the parent piece `T̂(p_1)` (when the type is not `three`). -/
def altEvenSubtiles (pre : Word) (aOdd : Standard.Tile) : List Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let Sq := (altShifts odd vp2 vq1).2
  let cof : AltQ0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altQ0Coeff odd x)
  [Standard.shift s.tOdd (cof .p1Plus), Standard.shift s.tOdd (cof .p1Minus),
    Standard.shift (doubled s.tEven Sq) (cof .dsQ1Plus), Standard.shift (doubled s.tEven Sq) (cof .dsQ1Minus)] ++
  (match altTypeOf pre with
    | none => []
    | some ty =>
      match altP1Coeff odd ty with
      | none => []
      | some c => [Standard.shift aOdd (coeffOff vp1 vp2 vq1 vq2 c)])

/-- The generator vectors `(v_{n/d,1}, v_{n/d,2})` of a fraction: `v_{n/d,1} = 2 𝔳_{n/d,1}` for an odd fraction and
`𝔳_{n/d,1}` for an even one, `v_{n/d,2} = 𝔳_{n/d,2}` (`Construction.OffsetTables`). -/
def childVectors (f : Fraction) : GInt × GInt :=
  (if (f.num + f.den) % 2 = 1 then texV1Odd f else texV1Even f, texV2 f)

/-- The neighbour vector `k₁ v₁ + k₂ v₂`. -/
def nbrVec (v1 v2 : GInt) (k1 k2 : ℤ) : GInt :=
  (k1 * v1.1 + k2 * v2.1, k1 * v1.2 + k2 * v2.2)

/-! ### Items (4) and (5): the readings (b) and (c) are isolated in one definition each -/

/-- Reading (b) of item (4), the surrounding (`lines 814-817`: the translates `T + k₁ v₁ + k₂ v₂`, `|k₁|, |k₂| ≤ 1`, diagonals
included). For each neighbour `v = k₁v₁ + k₂v₂ ≠ 0`, every point of the overlap `T ∩ (T + v)` lies in the stacked strings, or in a
whole subtile `s` of `T` that lies in the overlap. This is one reading of "consists of either part of a stacked zero-one boundary
string or a complete overlap on a subtile"; the operator is asked to confirm it. -/
def AltItem4Reading (T : Standard.Tile) (v1 v2 : GInt) (strings : Finset GInt) (subtiles : List Standard.Tile) : Prop :=
  ∀ k1 k2 : ℤ, -1 ≤ k1 → k1 ≤ 1 → -1 ≤ k2 → k2 ≤ 1 → (k1 ≠ 0 ∨ k2 ≠ 0) →
    ∀ x ∈ T, x ∈ Standard.shift T (nbrVec v1 v2 k1 k2) →
      x ∈ strings ∨ ∃ s ∈ subtiles, x ∈ s ∧ ∀ y ∈ s, y ∈ T ∧ y ∈ Standard.shift T (nbrVec v1 v2 k1 k2)

/-- Reading (c) of item (5). Two distinct subtiles that are neighbours (some points of them are at unit distance) share their
boundary: every common point of the two subtiles lies in the stacked strings. This is one reading of "the shared boundary
between neighboring subtiles is part of or is a stacked horizontal or vertical zero-one boundary string"; the operator is asked
to confirm it. -/
def AltItem5Reading (strings : Finset GInt) (subtiles : List Standard.Tile) : Prop :=
  ∀ s ∈ subtiles, ∀ t ∈ subtiles, s ≠ t →
    (∃ x ∈ s, ∃ y ∈ t, (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 = 1) →
      ∀ z ∈ s, z ∈ t → z ∈ strings

/-- Item (4) for the alternate children of the non-base words, with the stacked strings of each child as the parameter
`strings`. -/
def AltItem4 (base : Word → Standard.Tile × Standard.Tile) (strings : Word → Bool → Finset GInt) : Prop :=
  ∀ w : Word, ¬ FLatticePaper.Tiles.Standard.IsBase w →
    AltItem4Reading (altOddTile base w) (childVectors ((parentsAt w).current .odd)).1
        (childVectors ((parentsAt w).current .odd)).2 (strings w false) (altOddSubtiles w (altRegs base w).2) ∧
    AltItem4Reading (altEvenTile base w) (childVectors ((parentsAt w).current .even)).1
        (childVectors ((parentsAt w).current .even)).2 (strings w true) (altEvenSubtiles w (altRegs base w).1)

/-- Item (5) for the alternate children of the non-base words. -/
def AltItem5 (base : Word → Standard.Tile × Standard.Tile) (strings : Word → Bool → Finset GInt) : Prop :=
  ∀ w : Word, ¬ FLatticePaper.Tiles.Standard.IsBase w →
    AltItem5Reading (strings w false) (altOddSubtiles w (altRegs base w).2) ∧
    AltItem5Reading (strings w true) (altEvenSubtiles w (altRegs base w).1)

/-- Item (1), symmetry: the alternate odd child is 180-degree symmetric about some centre. -/
def AltItem1Symmetric (T : Standard.Tile) : Prop :=
  ∃ c : GInt, ∀ x : GInt, x ∈ T ↔ (2 * c.1 - x.1, 2 * c.2 - x.2) ∈ T

/-- Item (1), rotation: the rotation of the alternate tile of `w` is, up to a translation, the alternate tile of the rotated
word (the rotation exchanges the letters 2 and 3, `swapW`, and the parities). The translation is not fixed by the text. -/
def AltItem1Rotation (base : Word → Standard.Tile × Standard.Tile) (w : Word) : Prop :=
  (∃ v : GInt, Standard.rot (altOddTile base w) = Standard.shift (altEvenTile base (swapW w)) v) ∧
  (∃ v : GInt, Standard.rot (altEvenTile base w) = Standard.shift (altOddTile base (swapW w)) v)

end FLatticePaper.Tiles.SurgicalAltTiles
