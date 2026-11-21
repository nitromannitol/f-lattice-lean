import FLatticePaper.Tiles.PseudoSquareSites

namespace FLatticePaper.Tiles

/-! The intended placement of the four zero-one strings along the boundary walk (exploratory; the reading of
def:tile_boundary_strings, line 1626, that the base tiles of prop:base_cases satisfy).

The walk of `pseudoBoundaryWord (gPseudo w_h w_v)` from `c` runs along the four sides of the tile in order: the lower
side `w_1 = G(w_h)`, the right side `w_2 = G(w_v)`, the top side `hat(rev w_1)` and the left side `hat(rev w_2)`.
Its points are `c`, `B = c + Σw_1` (the end of the lower side), `C` (the end of the right side) and `D` (the end of the
top side, which is the start of the left side). Each string starts at the walk point where its side starts, shifted by
the corner of its first tile that lies on that side:
* the lower string `w_h` starts at `c` (the bottom-left corner of `T_{1/1}`),
* the right string `w_v` starts at `B - (1,0)` (the bottom-right corner of `T_{0/1}`),
* the top string `rev w_h` starts at `D - (0,2)` (the top-left corner of `T_{0/1}`),
* the left string `rev w_v` starts at `c` (the bottom-left corner of `T_{1/1}`).
The later tiles of each string follow the offsets of its zero-one string (lines 1266-1342). -/

/-- The points of the boundary walk of `(w_h, w_v)` from `c`, starting with `c`. -/
def boundaryWalk (c : GInt) (wh wv : BinaryWord) : List GInt :=
  F2Word.walk c (pseudoBoundaryWord (gPseudo wh wv).1 (gPseudo wh wv).2)

/-- The `k`-th point of the boundary walk. -/
def walkAt (c : GInt) (wh wv : BinaryWord) (k : ℕ) : GInt := (boundaryWalk c wh wv).getD k c

/-- The four strings with their placed tiles, along the walk. The lower and left strings start at `c`, the right string
at `B - (1,0)` where `B` is the walk point after the lower side, and the top string at `D - (0,2)` where `D` is the walk
point after the top side. -/
def alongStrings (wh wv : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  let n1 := (gPseudo wh wv).1.length
  let n2 := (gPseudo wh wv).2.length
  hStringAt wh c ++ hRevStringAt wh.reverse (walkAt c wh wv (n1 + n2 + n1) + (0, -2)) ++
    vRevStringAt wv.reverse c ++ vStringAt wv (walkAt c wh wv n1 + (-1, 0))

/-- The two clauses of the pseudo-square definition for the walk placement: the placed sites lie in `T`, and they cover
`∂⁻T`. The corner `c` is `c(T)` (line 1099). -/
def alongCheck (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c =>
    let sites := placedSites (alongStrings wh wv c)
    (sites.all fun x => T.contains x) && ((innerBoundaryList T).all fun x => sites.contains x)

/-- The pseudo-square predicate for the walk placement. -/
def IsPseudoSquareAlong (T : List GInt) (wh wv : BinaryWord) : Prop := alongCheck T wh wv = true

instance (T : List GInt) (wh wv : BinaryWord) : Decidable (IsPseudoSquareAlong T wh wv) :=
  inferInstanceAs (Decidable (_ = true))

end FLatticePaper.Tiles
