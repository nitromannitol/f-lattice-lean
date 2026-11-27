import FLatticePaper.Tiles.SurgicalOdometers
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! # The corner tiles A, B, C, D and the corner identities (in affine factors, see `SurgicalAffineChain.lean`) (surgical `lemma:weak_standard_odometer_properties`, (b))

Let `A, B, C, D` be the first and last tiles of the horizontal string `w_h` and the last and first tiles of `rev(w_h)`, placed
by the E07 anchors (`anchoredStrings`): `A` = first of `h^+`, `B` = last of `h^+`, `C` = last of `h^-`, `D` = first of `h^-`.
A corner tile is a zero or one tile, a point set (`placedSites` of the single placed tile). The restriction `o_Z` of a partial
odometer to a placed tile has its values on the tile; the affine factors of the corners are in `SurgicalAffineChain.lean`.

The identities of (b) (the printed text): `s(o_B) − s(o_A) = 0`, `s(o_C) − s(o_D) = a_{0/1,2} − a_{1/1,2}`,
`s(o_C) − s(o_B) = a_{n/d,2} − a_{1/1,2}`, with `a_{n/d,2} = (n, −d)`. This file gives the data; the odometer is a parameter. -/

namespace FLatticePaper.Tiles

/-- The four corner tiles of the horizontal side of a pseudo-square with words `(w_h, w_v)` at lower-left vertex `c`:
`(A, B, C, D)` = (first of `h^+`, last of `h^+`, last of `h^-`, first of `h^-`), as placed zero-one tiles. -/
def cornerTiles (wh wv : BinaryWord) (c : Site) : (ZTile × Site) × (ZTile × Site) × (ZTile × Site) × (ZTile × Site) :=
  let Hp := hStringAt wh c
  let Hm := hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse c))
  ((Hp.headD (.zero, 0)), (Hp.getLastD (.zero, 0)), (Hm.getLastD (.zero, 0)), (Hm.headD (.zero, 0)))

end FLatticePaper.Tiles
