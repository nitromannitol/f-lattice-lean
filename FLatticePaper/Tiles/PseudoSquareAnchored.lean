import FLatticePaper.Tiles.PseudoSquareSites

/-! # The pseudo-square predicate with the E07 anchoring (surgical `def:tile_boundary_strings`, line 1652 at 2540aed)

`PseudoSquareSites` places the four strings with the fixed stacking offsets `stackH` and `stackV`. The surgical text instead
anchors them at the last tiles of the other strings:

* `c(T_{1,h}^+) = c(T_{1,v}^-) = c(T)`;
* `c(T_{1,v}^+) = c(T_{|w_h|,h}^+)` (the position of the last horizontal forward tile);
* `c(T_{1,h}^-) = c(T_{|w_v|,v}^-)` (the position of the last vertical reversed tile).

This file adds the anchored predicate beside `PseudoSquareSites`, which is not modified (its proofs use the fixed offsets).
The two clauses are those of `IsPseudoSquareSites`: the strings lie in `T`, and they cover the inner boundary `∂⁻T`. -/

namespace FLatticePaper.Tiles

/-- The lower-left position of the last tile of a placed string (`0` for the empty string). -/
def lastPosOf (l : List (ZTile × GInt)) : GInt := (l.getLast?.map (·.2)).getD 0

/-- The four placed strings of a pseudo-square with corner `c`, with the E07 anchors. The order is that of `pseudoStrings`:
forward horizontal, reversed horizontal, reversed vertical, forward vertical. -/
def anchoredStrings (wh wv : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  let Hp := hStringAt wh c
  let Vm := vRevStringAt wv.reverse c
  let Vp := vStringAt wv (lastPosOf Hp)
  let Hm := hRevStringAt wh.reverse (lastPosOf Vm)
  Hp ++ Hm ++ Vm ++ Vp

/-- Clause 1 with the anchored strings: the strings lie in `T`. -/
def anchoredInside (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c => (placedSites (anchoredStrings wh wv c)).all fun x => T.contains x

/-- Clause 2 with the anchored strings: the strings cover `∂⁻T`. -/
def anchoredCovers (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c => (innerBoundaryList T).all fun x => (placedSites (anchoredStrings wh wv c)).contains x

/-- The `(w_h, w_v)`-pseudo-square predicate with the E07 anchoring, on a finite site set. -/
def IsPseudoSquareAnchored (T : List GInt) (wh wv : BinaryWord) : Prop :=
  anchoredInside T wh wv = true ∧ anchoredCovers T wh wv = true

instance (T : List GInt) (wh wv : BinaryWord) : Decidable (IsPseudoSquareAnchored T wh wv) :=
  inferInstanceAs (Decidable (_ ∧ _))

end FLatticePaper.Tiles
