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

/-! ### The standard subtiles of the alternate children, grouped by parent

Items (4) and (5) use the standard subtiles only (the alternate parent piece is not standard). Each child has two groups: the
pieces of the odd parent `p_1` and the pieces of the even parent `q_1` (operator's reading of item (5), 8824170). -/

/-- The standard subtiles of the odd alternate child of `pre` from the odd parent `p_1`: the doubled `T^{ds}(p_1)^±`. -/
def altOddPFam (pre : Word) : List Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let Sp := (altShifts odd vp2 vq1).1
  let cof : AltP0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altP0Coeff odd x)
  [Standard.shift (doubled s.tOdd Sp) (cof .dsP1Plus), Standard.shift (doubled s.tOdd Sp) (cof .dsP1Minus)]

/-- The standard subtiles of the odd alternate child of `pre` from the even parent `q_1`: the plain `T(q_1)^±`. -/
def altOddQFam (pre : Word) : List Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let cof : AltP0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altP0Coeff odd x)
  [Standard.shift s.tEven (cof .q1Plus), Standard.shift s.tEven (cof .q1Minus)]

/-- The standard subtiles of the even alternate child of `pre` from the odd parent `p_1`: the plain `T(p_1)^±`. -/
def altEvenPFam (pre : Word) : List Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let cof : AltQ0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altQ0Coeff odd x)
  [Standard.shift s.tOdd (cof .p1Plus), Standard.shift s.tOdd (cof .p1Minus)]

/-- The standard subtiles of the even alternate child of `pre` from the even parent `q_1`: the doubled `T^{ds}(q_1)^±`. -/
def altEvenQFam (pre : Word) : List Standard.Tile :=
  let s := stateAt pre
  let pf := parentsAt pre
  let odd := phase pre == 1
  let vp1 := texV1Odd pf.odd
  let vp2 := texV2 pf.odd
  let vq1 := texV1Even pf.even
  let vq2 := texV2 pf.even
  let Sq := (altShifts odd vp2 vq1).2
  let cof : AltQ0Piece → GInt := fun x => coeffOff vp1 vp2 vq1 vq2 (altQ0Coeff odd x)
  [Standard.shift (doubled s.tEven Sq) (cof .dsQ1Plus), Standard.shift (doubled s.tEven Sq) (cof .dsQ1Minus)]

/-- The generator vectors `(v_{n/d,1}, v_{n/d,2})` of a fraction: `v_{n/d,1} = 2 𝔳_{n/d,1}` for an odd fraction and
`𝔳_{n/d,1}` for an even one, `v_{n/d,2} = 𝔳_{n/d,2}` (`Construction.OffsetTables`). -/
def childVectors (f : Fraction) : GInt × GInt :=
  (if (f.num + f.den) % 2 = 1 then texV1Odd f else texV1Even f, texV2 f)

/-- The neighbour vector `k₁ v₁ + k₂ v₂`. -/
def nbrVec (v1 v2 : GInt) (k1 k2 : ℤ) : GInt :=
  (k1 * v1.1 + k2 * v2.1, k1 * v1.2 + k2 * v2.2)

/-! ### Items (4) and (5): the readings are isolated in one definition each (operator's answers, 8824170) -/

/-- Item (4) for one tile `T` with generators `v₁, v₂` and stacked strings `strings`, against the standard subtiles `std`: for
each neighbour `v = k₁v₁ + k₂v₂` with `|k₁|, |k₂| ≤ 1` and `v ≠ 0`, every point of `T ∩ (T + v)` lies in the stacked strings, or
in a whole standard subtile of one tile lying in the other (a subtile of `T` inside `T + v`, or a translate of a subtile of `T`
inside `T`). -/
def AltItem4Reading (T : Standard.Tile) (v1 v2 : GInt) (strings : Finset GInt) (std : List Standard.Tile) : Prop :=
  ∀ k1 k2 : ℤ, -1 ≤ k1 → k1 ≤ 1 → -1 ≤ k2 → k2 ≤ 1 → (k1 ≠ 0 ∨ k2 ≠ 0) →
    ∀ x ∈ T, x ∈ Standard.shift T (nbrVec v1 v2 k1 k2) →
      x ∈ strings ∨
      ∃ s ∈ std,
        (x ∈ s ∧ ∀ y ∈ s, y ∈ T ∧ y ∈ Standard.shift T (nbrVec v1 v2 k1 k2)) ∨
        (x ∈ Standard.shift s (nbrVec v1 v2 k1 k2) ∧
          ∀ y ∈ Standard.shift s (nbrVec v1 v2 k1 k2), y ∈ T ∧ y ∈ Standard.shift T (nbrVec v1 v2 k1 k2))

/-- Item (5) for the standard subtiles of two different parents, `P` (one parent) and `Q` (the other): two neighbouring subtiles
(their point sets intersect) share their common points only in the stacked strings. -/
def AltItem5Reading (strings : Finset GInt) (P Q : List Standard.Tile) : Prop :=
  ∀ s ∈ P, ∀ t ∈ Q, (∃ z, z ∈ s ∧ z ∈ t) → ∀ z ∈ s, z ∈ t → z ∈ strings

/-- Item (4) for the alternate children of the non-base words, with the stacked strings of each child as the parameter. -/
def AltItem4 (base : Word → Standard.Tile × Standard.Tile) (strings : Word → Bool → Finset GInt) : Prop :=
  ∀ w : Word, ¬ FLatticePaper.Tiles.Standard.IsBase w →
    AltItem4Reading (altOddTile base w) (childVectors ((parentsAt w).current .odd)).1
        (childVectors ((parentsAt w).current .odd)).2 (strings w false) (altOddPFam w ++ altOddQFam w) ∧
    AltItem4Reading (altEvenTile base w) (childVectors ((parentsAt w).current .even)).1
        (childVectors ((parentsAt w).current .even)).2 (strings w true) (altEvenPFam w ++ altEvenQFam w)

/-- Item (5) for the alternate children of the non-base words. -/
def AltItem5 (strings : Word → Bool → Finset GInt) : Prop :=
  ∀ w : Word, ¬ FLatticePaper.Tiles.Standard.IsBase w →
    AltItem5Reading (strings w false) (altOddPFam w) (altOddQFam w) ∧
    AltItem5Reading (strings w true) (altEvenPFam w) (altEvenQFam w)

/-- Item (1), symmetry: the alternate odd child is 180-degree symmetric about some centre. -/
def AltItem1Symmetric (T : Standard.Tile) : Prop :=
  ∃ c : GInt, ∀ x : GInt, x ∈ T ↔ (2 * c.1 - x.1, 2 * c.2 - x.2) ∈ T

/-- Item (1), rotation (operator's answer 8824170: up to a translation). The rotation of the alternate tile of `w` followed by the
translation with equal lower-left vertices is the alternate tile of the rotated word (`swapW w`, the parity exchanged). The lower-
left vertices are `lowerLeftList` of the point lists. -/
def AltItem1Rotation (base : Word → Standard.Tile × Standard.Tile) (w : Word) : Prop :=
  (∀ c c' : GInt,
    lowerLeftList (Standard.rot (altOddTile base w)).toList = some c →
    lowerLeftList (altEvenTile base (swapW w)).toList = some c' →
    Standard.shift (Standard.rot (altOddTile base w)) (c' - c) = altEvenTile base (swapW w)) ∧
  (∀ c c' : GInt,
    lowerLeftList (Standard.rot (altEvenTile base w)).toList = some c →
    lowerLeftList (altOddTile base (swapW w)).toList = some c' →
    Standard.shift (Standard.rot (altEvenTile base w)) (c' - c) = altOddTile base (swapW w))

end FLatticePaper.Tiles.SurgicalAltTiles
