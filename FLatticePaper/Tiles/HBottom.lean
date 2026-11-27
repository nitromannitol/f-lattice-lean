import FLatticePaper.Tiles.PseudoSquare
import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.SiteStrings

/-! The bottom walk of a horizontal string (H2, hB), first step: the displacement of a `gPair` segment.

A zero-one tile has an anchor: `zero` and `one` are anchored at their origin, the enlarged `oneD` at its origin plus `(1,-1)`.
Entering a tile moves the origin by `incr` (horizontal origin step: `(2,0)` for a `p`, `(1,1)` for a `q`, `dxdy`). For every pair
of consecutive tiles that the tile sequence produces, the walk segment `gPair a b` has displacement `incr b + off b - off a`. -/

namespace FLatticePaper.Tiles.HBottom

open FLatticePaper.Tiles FLatticePaper.Farey

/-- The anchor offset of a zero-one tile. -/
def anchorOff : ZTile → GInt
  | .zero => (0, 0)
  | .one => (0, 0)
  | .oneD => (1, -1)

/-- The origin increment of entering a tile. -/
def incr : ZTile → GInt
  | .zero => (2, 0)
  | .one => (1, 1)
  | .oneD => (1, 1)

/-- The pairs of consecutive tiles that `tileSeq` never produces are excluded. -/
def ValidPair (a b : ZTile) : Prop :=
  ¬ ((a = .zero ∧ b = .oneD) ∨ (a = .one ∧ b = .one) ∨ (a = .oneD ∧ b = .one))

/-- The displacement of the `gPair` segment of a valid pair is the origin step of its second tile, plus the anchor change. -/
theorem sum_gPair (a b : ZTile) (h : ValidPair a b) :
    F2Word.sum (gPair a b) = incr b + anchorOff b - anchorOff a := by
  cases a <;> cases b <;> simp_all [ValidPair, gPair, incr, anchorOff, F2Word.sum, Unit4.vec]

/-- The base sites of a zero-one tile, relative to its origin (`baseSites` of its letter; `oneD` is the enlarged `q`). -/
def baseOf : ZTile → List (ℤ × ℤ)
  | .zero => FLatticePaper.Tiles.SiteStrings.baseSites Letter.p false
  | .one => FLatticePaper.Tiles.SiteStrings.baseSites Letter.q false
  | .oneD => FLatticePaper.Tiles.SiteStrings.baseSites Letter.q true

/-- The points of the walk of a valid pair segment lie in the base sites of one of its two tiles (offsets from the origin of
the first tile, and from the origin of the second tile, which is `incr b` further). -/
theorem walk_gPair_mem (a b : ZTile) (h : ValidPair a b) (x : GInt)
    (hx : x ∈ F2Word.walk (anchorOff a) (gPair a b)) :
    x ∈ baseOf a ∨ x - incr b ∈ baseOf b := by
  have key : ∀ a b : ZTile, ValidPair a b →
      (F2Word.walk (anchorOff a) (gPair a b)).all
        (fun x => decide (x ∈ baseOf a) || decide (x - incr b ∈ baseOf b)) = true := by
    intro a b hab
    cases a <;> cases b <;> first | exact (hab (by decide)).elim | decide
  have hk := List.all_eq_true.1 (key a b h) x hx
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using hk

end FLatticePaper.Tiles.HBottom
