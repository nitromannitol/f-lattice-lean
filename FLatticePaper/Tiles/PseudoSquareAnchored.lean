import FLatticePaper.Tiles.PseudoSquareSites
import FLatticePaper.Tiles.PartialBoundary

/-! # The pseudo-square predicate with the E07 anchoring, on point sets (surgical `def:tile_boundary_strings`, line 1652)

The tile `T` is a set of lattice points (not of cells). `PseudoSquareSites` places the four strings with the fixed stacking
offsets `stackH` and `stackV`. The surgical text anchors them at the last tiles of the other strings:

* `c(T_{1,h}^+) = c(T_{1,v}^-) = c(T)`, where `c(T)` is the lower-left point `IsLowerLeftPt`;
* `c(T_{1,v}^+) = c(T_{|w_h|,h}^+)` (the position of the last horizontal forward tile);
* `c(T_{1,h}^-) = c(T_{|w_v|,v}^-)` (the position of the last vertical reversed tile).

The predicate asks that the strings lie in `T` (`InsideTile`) and cover the inner boundary `∂⁻T = {x ∈ T : ∃ y ∉ T, |y-x| = 1}`. -/

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

/-- The inner boundary `∂⁻T` of a point set: the points of `T` with a unit neighbour outside `T`. -/
def innerBoundaryPt (T : Set GInt) : Set GInt := {x | x ∈ T ∧ ∃ y, y ∉ T ∧ unitApart x y}

/-- The lattice points covered by placed tiles. -/
def placedSet (ts : List (ZTile × GInt)) : Set GInt := {x | x ∈ placedSites ts}

/-- The `(w_h, w_v)`-pseudo-square predicate with the E07 anchoring, on point sets: some lower-left point `c` of `T` anchors the
four strings, the strings lie in `T`, and they cover `∂⁻T`. -/
def IsPseudoSquareAnchoredPt (T : Set GInt) (wh wv : BinaryWord) : Prop :=
  ∃ c : GInt, IsLowerLeftPt T c ∧ InsideTile T (anchoredStrings wh wv c) ∧
    innerBoundaryPt T ⊆ placedSet (anchoredStrings wh wv c)

end FLatticePaper.Tiles
