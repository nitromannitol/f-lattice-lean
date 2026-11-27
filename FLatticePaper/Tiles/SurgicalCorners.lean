import FLatticePaper.Tiles.SurgicalOdometers
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! # The corner tiles A, B, C, D and the corner slope identities (surgical `lemma:weak_standard_odometer_properties`, (b))

Let `A, B, C, D` be the first and last tiles of the horizontal string `w_h` and the last and first tiles of `rev(w_h)`, placed
by the E07 anchors (`anchoredStrings`): `A` = first of `h^+`, `B` = last of `h^+`, `C` = last of `h^-`, `D` = first of `h^-`.
A corner tile is a zero or one tile, a point set (`placedSites` of the single placed tile). The restriction `o_Z` of a partial
odometer to `Z` has domain `o.dom ∩ Z`; its slope is `PartialOdometer.slope`.

The identities of (b) (the printed text): `s(o_B) − s(o_A) = 0`, `s(o_C) − s(o_D) = a_{0/1,2} − a_{1/1,2}`,
`s(o_C) − s(o_B) = a_{n/d,2} − a_{1/1,2}`, with `a_{n/d,2} = (n, −d)`. This file gives the data; the odometer is a parameter. -/

namespace FLatticePaper.Tiles

/-- The point set of one placed zero-one tile. -/
noncomputable def placedPoints (t : ZTile × Site) : Finset Site :=
  (placedSites [t]).toFinset

/-- The four corner tiles of the horizontal side of a pseudo-square with words `(w_h, w_v)` at lower-left vertex `c`:
`(A, B, C, D)` = (first of `h^+`, last of `h^+`, last of `h^-`, first of `h^-`), as placed zero-one tiles. -/
def cornerTiles (wh wv : BinaryWord) (c : Site) : (ZTile × Site) × (ZTile × Site) × (ZTile × Site) × (ZTile × Site) :=
  let Hp := hStringAt wh c
  let Hm := hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse c))
  ((Hp.headD (.zero, 0)), (Hp.getLastD (.zero, 0)), (Hm.getLastD (.zero, 0)), (Hm.headD (.zero, 0)))

/-- The corner slope identities of (b), for an odometer `o` with the four corner tiles `A, B, C, D` (as point sets). -/
noncomputable def CornerSlopeIdentities (n d : ℤ) (o : PartialOdometer) (A B C D : Finset Site) : Prop :=
  (({ dom := o.dom ∩ B, val := o.val } : PartialOdometer).slope -
      ({ dom := o.dom ∩ A, val := o.val } : PartialOdometer).slope = 0) ∧
  (({ dom := o.dom ∩ C, val := o.val } : PartialOdometer).slope -
      ({ dom := o.dom ∩ D, val := o.val } : PartialOdometer).slope =
      (((offsetA 0 1 true).1 : ℚ), ((offsetA 0 1 true).2 : ℚ)) -
        (((offsetA 1 1 true).1 : ℚ), ((offsetA 1 1 true).2 : ℚ))) ∧
  (({ dom := o.dom ∩ C, val := o.val } : PartialOdometer).slope -
      ({ dom := o.dom ∩ B, val := o.val } : PartialOdometer).slope =
      (((offsetA n d true).1 : ℚ), ((offsetA n d true).2 : ℚ)) -
        (((offsetA 1 1 true).1 : ℚ), ((offsetA 1 1 true).2 : ℚ)))

end FLatticePaper.Tiles
