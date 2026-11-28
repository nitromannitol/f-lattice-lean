import FLatticePaper.Tiles.JointInduction
import FLatticePaper.Tiles.JointGlue

/-! # Local compatibility inputs of the tile step (Section 8, Cases 1-4)

The tile step glues the pieces of the tile decompositions (`tileOddPieces`, `tileEvenPieces`, `tileAltOddPieces`,
`tileAltEvenPieces`) with `JointGlue.agree_of_compatible`, whose local hypothesis is that two overlapping pieces differ by a
constant on their overlap (`PairCompat`). Two families of pairs are not covered by the closed-path inputs of the standard and
alternate children (`ClosedPathAlt.AltMixedCompatOdd/Even` quantify only the six standard copies), and are stated here as named
inputs. Both are statements, not proved here:
* `AltParentCompatInput` (Section 8, Case 3): the alternate parent piece, entry `6` of the alternate decompositions, against each
  of the six standard copies.
* `CorrectedCompatInput` (Section 8, Cases 2 and 4): in a corrected tile decomposition, each L-correction entry against each full
  copy. -/

namespace FLatticePaper.Tiles.TileCompatInputs

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.Standard (IsBase)

/-- Local compatibility of the entries `i` and `j` of a decomposition: the placed odometers (with their affine factors) differ by a
constant on the overlap of the placed domains, outside the exceptional points. Vacuous when an entry is missing. -/
def PairCompat (ps : List Piece) (i j : ℕ) : Prop :=
  ∀ p q : Piece, ps[i]? = some p → ps[j]? = some q →
    ∃ c : ℤ, ∀ x ∈ p.placed, x ∈ q.placed → x ∉ p.exc → x ∉ q.exc → pieceVal p x - pieceVal q x = c

/-- The entries of `tileOddPieces` that are L-corrections at a corrected odd child (after a `3`). -/
def oddLIdx (w : Word) : List ℕ := if W1Odd w then [2, 5] else [3, 4]

/-- The entries of `tileEvenPieces` that are L-corrections at a corrected even child (after a `2`). -/
def evenLIdx : List ℕ := [1, 2]

/-- The entries of `tileAltOddPieces` that are L-corrections at a corrected odd alternate child (after a `2`). -/
def altOddLIdx : List ℕ := [1, 2]

/-- The entries of `tileAltEvenPieces` that are L-corrections at a corrected even alternate child (after a `3`). -/
def altEvenLIdx : List ℕ := [0, 3]

/-- **Section 8, Case 3**: the alternate parent piece (entry `6` of the alternate decompositions, when the type of `w` keeps it)
is compatible with each of the six standard copies, over the family below `w`. -/
def AltParentCompatInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ¬ IsBase w → ∀ j < 6,
    PairCompat (tileAltOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w) 6 j ∧
      PairCompat (tileAltEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w) 6 j

/-- **Section 8, Cases 2 and 4**: in a corrected tile decomposition, each L-correction entry is compatible with each full copy
(the other entries among the six), over the family below `w`; for the standard and the alternate decompositions. -/
def CorrectedCompatInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ¬ IsBase w →
    (CorrectedAfterThree w → ∀ i ∈ oddLIdx w, ∀ j < 6, j ∉ oddLIdx w →
      PairCompat (tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).lEven) w) i j) ∧
    (CorrectedAfterTwo w → ∀ i ∈ evenLIdx, ∀ j < 6, j ∉ evenLIdx →
      PairCompat (tileEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).lOdd) w) i j) ∧
    (CorrectedAfterTwo w → ∀ i ∈ altOddLIdx, ∀ j < 6, j ∉ altOddLIdx →
      PairCompat (tileAltOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w) i j) ∧
    (CorrectedAfterThree w → ∀ i ∈ altEvenLIdx, ∀ j < 6, j ∉ altEvenLIdx →
      PairCompat (tileAltEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w) i j)

end FLatticePaper.Tiles.TileCompatInputs
