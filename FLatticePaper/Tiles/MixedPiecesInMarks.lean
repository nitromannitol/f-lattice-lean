import FLatticePaper.Tiles.SiteInduction

/-! (d) of `lemma:standard_tile_properties`, in point-set form, stated as a proposition (no proof here).

For a non-base word `w`, the odd child of `w` is the union of the copies of its odd register `T1 = (stateAt w).tOdd` (the
parent `p`) and of its even register `T2 = (stateAt w).tEven` (the parent `q`), at the offsets of `oddChildB`; the even child
is the same with the offsets of `evenChildB`. The offset lists below are read off those two definitions, copy by copy.

`MixedPiecesInMarks w` says: when a copy of `T1` at offset `a` and a copy of `T2` at offset `b` meet at a site `z`, that site
lies in the marked strings of both copies, that is in `shiftS (marksOdd u1) a` and in `shiftS (marksEven u2) b`. Here
`u1`, `u2` are words with `T1 = oddTile u1` and `T2 = evenTile u2` (`regOdd_exists`, `regEven_exists`). The marks of a
translated tile are the translated marks (`lowLeft` and `halfTurn` are covariant), so `shiftS` is the marks of the copy.

Only copies of different parents are claimed. The overlaps of two copies of the same parent lie inside the tile, and the
existence step deletes them first (`lemma:tile-odometer-existence`, Step 1). The numerical check of this statement is in the
worker notes: all 3772 mixed pairs of words of length at most 5 satisfy it, and the stronger claim with the inner boundary
of both copies fails (an overlap site can be interior to one copy). -/

namespace FLatticePaper.Tiles.MixedPiecesInMarks

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteInduction

/-- Offsets of the copies of the odd register `T1` (parent `p`) in the odd child: `oddChildB`, first argument `flag`
(the phase of the word is odd). In the first case the copies are `T1` and `T1` shifted by `2 v_{q,1} + v_{q,2}`. -/
def pOffsetsOdd (flag : Bool) (p q : Fraction) : List (ℤ × ℤ) :=
  if flag then [0, texV1Even q + texV1Even q + texV2 q]
  else [texV1Even q + texV1Even q, texV2 q]

/-- Offsets of the copies of the even register `T2` (parent `q`) in the odd child, following `oddChildB`. -/
def qOffsetsOdd (flag : Bool) (p q : Fraction) : List (ℤ × ℤ) :=
  if flag then [texV1Odd p, texV1Odd p + texV1Even q, texV2 p, texV2 p + texV1Even q]
  else [0, texV1Even q, texV1Odd p + texV2 p, texV1Odd p + texV2 p + texV1Even q]

/-- Offsets of the copies of the odd register `T1` (parent `p`) in the even child, following `evenChildB`. -/
def pOffsetsEven (flag : Bool) (p q : Fraction) : List (ℤ × ℤ) :=
  if flag then [0, texV2 p, texV1Even q + texV2 q, texV1Even q + texV2 q + texV2 p]
  else [texV1Even q, texV1Even q + texV2 p, texV2 q, texV2 q + texV2 p]

/-- Offsets of the copies of the even register `T2` (parent `q`) in the even child, following `evenChildB`. -/
def qOffsetsEven (flag : Bool) (p q : Fraction) : List (ℤ × ℤ) :=
  if flag then [texV1Odd p, texV2 p + texV2 p]
  else [0, texV1Odd p + (texV2 p + texV2 p)]

/-- The mixed-piece claim for the odd child of `w`, over the registers `u1` (odd) and `u2` (even). -/
def MixedPiecesInMarksOdd (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ a ∈ pOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ qOffsetsOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z : ℤ × ℤ,
      z ∈ shiftS ((oddTile u1 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) a →
      z ∈ shiftS ((evenTile u2 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) b →
      z ∈ shiftS (marksOdd u1) a ∧ z ∈ shiftS (marksEven u2) b

/-- The mixed-piece claim for the even child of `w`, over the same two registers. -/
def MixedPiecesInMarksEven (w : Word) : Prop :=
  ∀ u1 u2 : Word, (stateAt w).tOdd = oddTile u1 → (stateAt w).tEven = evenTile u2 →
    ∀ a ∈ pOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ b ∈ qOffsetsEven (phase w == 1) (parentsAt w).odd (parentsAt w).even,
    ∀ z : ℤ × ℤ,
      z ∈ shiftS ((oddTile u1 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) a →
      z ∈ shiftS ((evenTile u2 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) b →
      z ∈ shiftS (marksOdd u1) a ∧ z ∈ shiftS (marksEven u2) b

/-- (d) at a word: both children satisfy the mixed-piece claim. -/
def MixedPiecesInMarks (w : Word) : Prop :=
  MixedPiecesInMarksOdd w ∧ MixedPiecesInMarksEven w

/-- (d) for every non-base word. This is the named input of the existence step; it is open until proved. -/
def MixedPiecesInMarksAll : Prop :=
  ∀ w : Word, ¬ IsBase w → MixedPiecesInMarks w

end FLatticePaper.Tiles.MixedPiecesInMarks
