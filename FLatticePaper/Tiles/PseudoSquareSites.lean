import FLatticePaper.Tiles.PseudoSquare

namespace FLatticePaper.Tiles

/-! The pseudo-square definition taken literally (def:tile_boundary_strings, lines 1626-1636), for a tile given as a
finite site set (a list without repetitions). A tile `T` is a `(w_h, w_v)`-pseudo-square when its four zero-one strings,
with the words `w_h`, `rev w_h`, `w_v`, `rev w_v`, lie in `T` and cover its inner boundary `∂⁻T` (line 2312).

The stacking offsets of the four strings are not all determined by the text, and the literal signs fail on the base tile
of d = 3 (see `checks/PseudoSquareSites.lean`). The conventions below are the ones under which that tile satisfies the
definition. Each is documented where it is used. -/

/-- The vertices of a horizontal zero-one tile type relative to its corner (lines 1262-1274): `T_{0/1}` is
`{0, i, 2i, 1, 1+i, 1+2i}`, `T_{1/1}` is `{0, i, 1, 1+i}`, and `T^d_{1/1} = T_{1/1} ∪ {i-1, 1-i}` (line 1276). -/
def tileShape : ZTile → List GInt
  | .zero => [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
  | .one => [(0, 0), (0, 1), (1, 0), (1, 1)]
  | .oneD => [(0, 0), (0, 1), (1, 0), (1, 1), (-1, 1), (1, -1)]

/-- The horizontal offset of a tile of letter `x` (eq:zero-one-bs, lines 1266-1274): `v_{p,1} = 2`, `v_{q,1} = 1+i`,
keyed by the letter of the tile itself. -/
def hOffset : Letter → GInt
  | .p => (2, 0)
  | .q => (1, 1)

/-- The reversed horizontal offset, keyed by the tuple `(T_{i-1}, T_i)` (eq:zero-one-bs-reversed, lines 1292-1302):
`pq ↦ v_{q,1} + 1`, `pp ↦ v_{p,1}`, `qp ↦ v_{p,1} - 1`, `qq ↦ v_{q,1}`. -/
def hRevOffset : Letter → Letter → GInt
  | .p, .q => (2, 1)
  | .p, .p => (2, 0)
  | .q, .p => (1, 0)
  | .q, .q => (1, 1)

/-- The vertical offset of a tile of letter `x` (eq:zero-one-bs-vertical, lines 1329-1334): `v_{p,2} = -1+i`,
`v_{q,2} = 2i`. -/
def vOffset : Letter → GInt
  | .p => (-1, 1)
  | .q => (0, 2)

/-- The reversed vertical offset, keyed by `(T_{i-1}, T_i)` (eq:zero-one-bs-reversed-vertical, lines 1336-1342):
`pq ↦ v_{p,2} + i`, `pp ↦ v_{p,2}`, `qp ↦ v_{q,2} - i`, `qq ↦ v_{q,2}`. -/
def vRevOffset : Letter → Letter → GInt
  | .p, .q => (-1, 2)
  | .p, .p => (-1, 1)
  | .q, .p => (0, 1)
  | .q, .q => (0, 2)

/-- The tile type of a letter in a non-doubled string: `p ↦ T_{0/1}`, `q ↦ T_{1/1}`. -/
def letterZTile : Letter → ZTile
  | .p => .zero
  | .q => .one

/-- The horizontal zero-one string `B_w` with its tile types and positions. Doubling is the rule of line 1276; the first
tile is at the given corner. Convention: the first letter of `w` is `q` (a horizontal string begins with `T_{1/1}`,
line 1281). -/
def hStringAt (w : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  (tileSeq w).zip (List.scanl (· + ·) c (w.tail.map hOffset))

/-- The reversed horizontal string `B^r_u` with its positions. Convention: no doubling in reversed strings, and the first
letter of `u` is `p` (a reversed horizontal string begins with `T_{0/1}`, line 1281). -/
def hRevStringAt (u : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  (u.map letterZTile).zip
    (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => hRevOffset ab.1 ab.2))

/-- The vertical zero-one string `B_w` (no doubling; the first letter of `w` is `p`, line 1348). -/
def vStringAt (w : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  (w.map letterZTile).zip (List.scanl (· + ·) c (w.tail.map vOffset))

/-- The reversed vertical string `B^r_u` (the first letter of `u` is `q`, line 1348). -/
def vRevStringAt (u : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  (u.map letterZTile).zip
    (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2))

/-- The stacking offset of the reversed horizontal string from the forward one. The text gives
`c(T^{+,1}) - c(T^{-,1}) = v_{p,2} + i` (line 1287). With that sign the d = 3 tile fails (its reversed string lies below
`T`), so the offset is taken with the opposite sign: `c(T^{-,1}) = c(T^{+,1}) + (v_{p,2} + i)`. -/
def stackH : GInt := (-1, 2)

/-- The stacking offset of the forward vertical string from the reversed one. The text gives
`c(T^{+,1}) - c(T^{-,1}) = -v_{q,1}` (line 1345), which places the d = 3 tile outside `T`. The offset that places it is
`c(T^{+,1}) = c(T^{-,1}) + v_{p,1}`, with `v_{p,1} = 2`: the first tile of the forward vertical string is a `p`. -/
def stackV : GInt := (2, 0)

/-- The four strings of a pseudo-square with corner `c`: the forward horizontal string of `w_h` at `c` (so that
`c(T^+_{1,h}) = c`), the reversed horizontal string of `rev w_h` stacked by `stackH`, the reversed vertical string of
`rev w_v` at `c` (so that `c(T^-_{1,v}) = c`), and the forward vertical string of `w_v` stacked by `stackV`. -/
def pseudoStrings (wh wv : BinaryWord) (c : GInt) : List (ZTile × GInt) :=
  hStringAt wh c ++ hRevStringAt wh.reverse (c + stackH) ++
    vRevStringAt wv.reverse c ++ vStringAt wv (c + stackV)

/-- The sites covered by a list of placed tiles. -/
def placedSites (ts : List (ZTile × GInt)) : List GInt :=
  ts.flatMap fun t => (tileShape t.1).map (· + t.2)

/-- The four lattice neighbours of a site. -/
def unitNeighbours (x : GInt) : List GInt :=
  [(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)]

/-- `∂⁻T`: the sites of `T` with a unit neighbour outside `T` (line 2312). -/
def innerBoundaryList (T : List GInt) : List GInt :=
  T.filter fun x => (unitNeighbours x).any fun y => !(T.contains y)

/-- The lower-left vertex `c(T)` (line 1099): the smallest imaginary part, then the smallest real part. -/
def lowerLeftList : List GInt → Option GInt
  | [] => none
  | x :: xs => some (xs.foldl (fun a b => if b.2 < a.2 ∨ (b.2 = a.2 ∧ b.1 < a.1) then b else a) x)

/-- Clause 1 of the definition: the four strings lie in `T`. -/
def stringsInside (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c => (placedSites (pseudoStrings wh wv c)).all fun x => T.contains x

/-- Clause 2 of the definition: the four strings cover `∂⁻T`. -/
def coversBoundary (T : List GInt) (wh wv : BinaryWord) : Bool :=
  match lowerLeftList T with
  | none => false
  | some c => (innerBoundaryList T).all fun x => (placedSites (pseudoStrings wh wv c)).contains x

/-- The literal `(w_h, w_v)`-pseudo-square predicate on a finite site set: both clauses hold. -/
def IsPseudoSquareSites (T : List GInt) (wh wv : BinaryWord) : Prop :=
  stringsInside T wh wv = true ∧ coversBoundary T wh wv = true

instance (T : List GInt) (wh wv : BinaryWord) : Decidable (IsPseudoSquareSites T wh wv) :=
  inferInstanceAs (Decidable (_ ∧ _))

end FLatticePaper.Tiles
