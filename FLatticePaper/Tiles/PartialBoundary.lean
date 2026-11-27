import FLatticePaper.Tiles.PseudoSquareSites
import FLatticePaper.Tiles.ZeroOneOdometers
import FLatticePaper.Tiles.SurgicalSlopes

/-! # Partial tile boundary strings (`def:partial_tile_boundary_strings`, surgical lines 1754-1766, 2540aed)

A `w_h`- or `w_v`-pseudo-square is a tile `T` which can be decomposed along part of its boundary into the subtiles
`T_{h,*} = {T_{i,h}^+} ∪ {T_{i,h}^-}` or `T_{*,v} = {T_{i,v}^+} ∪ {T_{i,v}^-}`, where `T` is as in
`def:tile_boundary_strings` and either `c(T) = c(T_{1,h}^+)` or `c(T) = c(T_{1,v}^-)` (operator, 2540aed: the full definition
minus its covering condition). So the subtiles lie in `T`, they form the stated zero-one strings, one string is anchored at
`c(T)`, and the other string's first position is free. The strings run along the inner boundary but need not cover it.

A partial odometer `S` respects `w_h` (resp. `w_v`) when, on each tile `T_i` of the family, `S` equals a zero- or one-odometer
`o_i` (the enlarged one-odometer on an enlarged tile), and the family `{o_i}` respects the string: the slope changes of
`eq:zero-one-odometer_slopes-horizontal` and `-vert` (exchanged for a reversed horizontal string), and the condition across
consecutive non-overlapping tiles. Respect is as for full tiles (operator), except that a single function `S` on `T` makes the
common-extension check automatic, so it is not stated again.

The definitions are statements only; no lemma about them is claimed here. -/

namespace FLatticePaper.Tiles

/-- The letter of a placed zero-one tile: the zero tile is `p`; the one tiles (including the enlarged one tile) are `q`. -/
def zTileLetter : ZTile → Letter
  | .zero => .p
  | .one => .q
  | .oneD => .q

/-- The base odometer of a tile type: the zero-odometer, the one-odometer, and the enlarged one-odometer on the enlarged one
tile, which equals the one-odometer on `T_{1/1}`, with value `-2` at `i - 1` and `0` at `1 - i` (line 1558). -/
def zTileOdo : ZTile → Site → ℤ
  | .zero => zeroOdometer
  | .one => oneOdometer
  | .oneD => fun x => if x = ((-1 : ℤ), (1 : ℤ)) then -2 else oneOdometer x

/-- `T_{h,*} = {T_{i,h}^+} ∪ {T_{i,h}^-}`: the forward horizontal string of `w_h` at `c` and the reversed horizontal string
of `rev w_h` at `c'`. -/
def hPartialTiles (wh : BinaryWord) (c c' : GInt) : List (ZTile × GInt) :=
  hStringAt wh c ++ hRevStringAt wh.reverse c'

/-- `T_{*,v} = {T_{i,v}^+} ∪ {T_{i,v}^-}`: the reversed vertical string of `rev w_v` at `c` and the forward vertical string of
`w_v` at `c'`. -/
def vPartialTiles (wv : BinaryWord) (c c' : GInt) : List (ZTile × GInt) :=
  vRevStringAt wv.reverse c ++ vStringAt wv c'

/-- The placed tiles lie in `T` (the first clause of `def:tile_boundary_strings`; the covering clause is not part of this
definition). -/
def InsideTile (T : List GInt) (ts : List (ZTile × GInt)) : Prop :=
  ∀ x ∈ placedSites ts, x ∈ T

/-- A family of placed zero-one and enlarged one tiles with affine parameters: the `k`-th odometer is the base odometer of its
tile type, translated to its position, plus `a_k · x + b_k`. -/
structure PTFamily where
  ts : List (ZTile × GInt)
  a : ℕ → GInt
  b : ℕ → ℤ

namespace PTFamily

/-- The `k`-th placed tile (with a default for indices beyond the list). -/
def tile (F : PTFamily) (k : ℕ) : ZTile × GInt := F.ts.getD k (ZTile.zero, (0 : GInt))

/-- The number of tiles. -/
def n (F : PTFamily) : ℕ := F.ts.length

/-- The `k`-th odometer on the site `x`. -/
def odo (F : PTFamily) (k : ℕ) (x : GInt) : ℤ :=
  zTileOdo (F.tile k).1 (x - (F.tile k).2) + (F.a k).1 * x.1 + (F.a k).2 * x.2 + F.b k

/-- The domain of the `k`-th odometer: the shape of its tile, translated to its position. -/
def dom (F : PTFamily) (k : ℕ) : List GInt :=
  (tileShape (F.tile k).1).map (· + (F.tile k).2)

end PTFamily

/-- Two sites at unit distance. -/
def unitApart (x y : GInt) : Prop := (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1

/-- The dot product of two sites. -/
def ptDot (v x : GInt) : ℤ := v.1 * x.1 + v.2 * x.2

/-- The family `F` respects the string of orientation `o` (reversed when `rev`): for each consecutive pair of tiles the slope
change is the table value, and for consecutive non-overlapping tiles the boundary condition holds after a shared translation
by the affine factor `a_i` of the first tile of the pair (the constants `b` absorb the rest): horizontally
`o_i(x) - a_i·x = o_{i+1}(y) - a_i·y` for unit-apart `x, y`; vertically `(o_{i+1}(y) - a_i·y) - (o_i(x) - a_i·x) = -1`.
(The shared translation is the one that the operator's model uses, and it is needed: without it the cross system of the
vertical Moreover is inconsistent, scratchpad `vert_debug.py`.) -/
def PTFamily.Respects (o : Orientation) (rev : Bool) (F : PTFamily) : Prop :=
  ∀ k, k + 1 < F.n →
    slopeOf (F.odo (k + 1)) (F.dom (k + 1)) - slopeOf (F.odo k) (F.dom k) =
        surgicalSlopeDiff o rev (zTileLetter (F.tile k).1) (zTileLetter (F.tile (k + 1)).1) ∧
      ((¬ ∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) →
        ∀ x ∈ F.dom k, ∀ y ∈ F.dom (k + 1), unitApart x y →
          (o = .horizontal →
              F.odo k x - ptDot (F.a k) x = F.odo (k + 1) y - ptDot (F.a k) y) ∧
            (o = .vertical →
              (F.odo (k + 1) y - ptDot (F.a k) y) - (F.odo k x - ptDot (F.a k) x) = -1))

/-- The partial odometer `S` restricted to the placed tiles `ts` respects the string: there is a family on exactly these tiles,
`S` equals its odometer on each of its domains, and the family respects the string (reversed when `rev`). -/
def RespectsTiles (o : Orientation) (rev : Bool) (ts : List (ZTile × GInt)) (S : GInt → ℤ) : Prop :=
  ∃ F : PTFamily, F.ts = ts ∧ (∀ k < F.n, ∀ x ∈ F.dom k, S x = F.odo k x) ∧ F.Respects o rev

/-- A `w_h`-pseudo-square (partial): `c(T) = c(T_{1,h}^+)`, and the subtiles `T_{h,*}` lie in `T`. -/
def IsPartialH (T : List GInt) (wh : BinaryWord) : Prop :=
  ∃ c c' : GInt, lowerLeftList T = some c ∧ InsideTile T (hPartialTiles wh c c')

/-- A `w_v`-pseudo-square (partial): `c(T) = c(T_{1,v}^-)`, and the subtiles `T_{*,v}` lie in `T`. -/
def IsPartialV (T : List GInt) (wv : BinaryWord) : Prop :=
  ∃ c c' : GInt, lowerLeftList T = some c ∧ InsideTile T (vPartialTiles wv c c')

/-- A `w_h` or `w_v`-pseudo-square (partial). -/
def IsPartialPseudoSquare (T : List GInt) (wh wv : BinaryWord) : Prop :=
  IsPartialH T wh ∨ IsPartialV T wv

/-- A partial odometer `S` on a `w_h`-pseudo-square `T`: the subtiles lie in `T` at the anchors `c = c(T)` and `c'`, the forward
string of `w_h` and the reversed string of `rev w_h` are respected by `S`. -/
def RespectsPartialH (T : List GInt) (wh : BinaryWord) (S : GInt → ℤ) : Prop :=
  ∃ c c' : GInt, lowerLeftList T = some c ∧ InsideTile T (hPartialTiles wh c c') ∧
    RespectsTiles .horizontal false (hStringAt wh c) S ∧
    RespectsTiles .horizontal true (hRevStringAt wh.reverse c') S

/-- A partial odometer `S` on a `w_v`-pseudo-square `T`: the subtiles lie in `T` at the anchors `c = c(T)` and `c'`, the reversed
string of `rev w_v` and the forward string of `w_v` are respected by `S`. -/
def RespectsPartialV (T : List GInt) (wv : BinaryWord) (S : GInt → ℤ) : Prop :=
  ∃ c c' : GInt, lowerLeftList T = some c ∧ InsideTile T (vPartialTiles wv c c') ∧
    RespectsTiles .vertical true (vRevStringAt wv.reverse c) S ∧
    RespectsTiles .vertical false (vStringAt wv c') S

/-- The partial odometer `S` on `T` respects `w_h` or `w_v`. -/
def RespectsPartial (T : List GInt) (wh wv : BinaryWord) (S : GInt → ℤ) : Prop :=
  RespectsPartialH T wh S ∨ RespectsPartialV T wv S

end FLatticePaper.Tiles
