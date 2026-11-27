import FLatticePaper.Tiles.ZeroOneOdometers

/-! # Partial odometers, slopes, offsets and the respect relations (surgical edition, Section 7 data)

A partial odometer is a function `h : T → ℤ` on a point set `T` (`dom`), with the slope `s(h)` of `T` defined as the average of
the square terms over the unit squares contained in `T` (surgical Section 5, the definition of a partial odometer; the slope
is `ZeroOneOdometers.slopeOf`). The offsets `a_{n/d,1} = 0`, `a_{n/d,2} = (n, −d)` (the printed `a = M(n,d) v`, surgical line
417–421) are integer vectors. Two partial odometers are translations (`IsTranslationOf`) and respect the tile translations
(`RespectTileTranslations`, surgical def. around line 3375), and two weak odometers are lattice adjacent (`LatticeAdjacent`,
surgical line 3410–3418). Everything here is data; the existence and the properties of weak standard odometers are not in this
file. -/

namespace FLatticePaper.Tiles

/-- A partial odometer on a point set: its domain (a list of lattice points) and its values. -/
structure PartialOdometer where
  dom : List Site
  val : Site → ℤ

/-- The slope `s(h)` of a partial odometer: the average over the unit squares of its domain (`slopeOf`). -/
def PartialOdometer.slope (h : PartialOdometer) : ℚ × ℚ :=
  slopeOf h.val h.dom

/-- The offset `a_{n/d,i}` for `i = 1` (`false`) and `i = 2` (`true`): `a_{n/d,1} = (0,0)`, `a_{n/d,2} = (n, −d)`. -/
def offsetA (n d : ℤ) : Bool → ℤ × ℤ
  | false => (0, 0)
  | true => (n, -d)

/-- `o_1` and `o_2` are translations of one another by `v` with affine correction `a^T x + b` (surgical definition of
translations): the domain of `o_1` is that of `o_2` moved by `v`, and `o_1(x) = o_2(x − v) + a^T x + b` on it. -/
def IsTranslationOf (o₁ o₂ : PartialOdometer) (v a : ℤ × ℤ) (b : ℤ) : Prop :=
  o₁.dom = o₂.dom.map (· + v) ∧
    ∀ x ∈ o₁.dom, o₁.val x = o₂.val (x - v) + (a.1 * x.1 + a.2 * x.2) + b

/-- Two partial odometers `o(n/d)` and `o(n'/d')` respect the tile translations for `i` (surgical def., line 3375): the slope
of `o(n'/d')` minus the slope of `o(n/d)` is `a_{n/d,i}`, and the domains are the tiles `T(n/d)` and `T(n'/d')`. -/
def RespectTileTranslations (n d : ℤ) (i : Bool) (T T' : List Site) (o o' : PartialOdometer) : Prop :=
  o.dom = T ∧ o'.dom = T' ∧
    o'.slope - o.slope = (((offsetA n d i).1 : ℚ), ((offsetA n d i).2 : ℚ))

/-- Lattice adjacency of two weak odometers (surgical line 3410–3418): the lower-left vertices differ by `v_{n/d,i}` and the
slopes differ by `a_{n/d,i}`. -/
def LatticeAdjacent (n d : ℤ) (i : Bool) (c c' : Site) (vi : Site) (o o' : PartialOdometer) : Prop :=
  c - c' = vi ∧ o.slope - o'.slope = (((offsetA n d i).1 : ℚ), ((offsetA n d i).2 : ℚ))

end FLatticePaper.Tiles
