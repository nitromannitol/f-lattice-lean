import FLatticePaper.Tiles.SurgicalPartial
import FLatticePaper.Tiles.SurgicalOdometers
import FLatticePaper.Tiles.SiteStrings

/-! Clause (2) of `def:standard_odometer_doubling`, defined from `def:partial_tile`.

The text: `d(o)^±_{n/d} = o_{n/d} ∪ o*_{n/d}` with `o*` on the partial tile `T^{h±/v±} + v_{n/d}`, and "after being restricted to
the relevant zero-one boundary strings, `o*` and `o` respect the tile translations" (surgical line 3377). Respect of the tile
translations (line 3375): the slope of the second odometer minus the slope of the first is `a_{n/d,i}`.

Here the relevant string is the side string of the partial tile: `T^{h±/v±}` coincides with `T` on one side `s` (`def:partial_tile`,
line 3317), and that side's string is `sideString wh wv c s` (`SurgicalPartial`). The first copy restricts to that string placed
at `c = 0` (the normalisation of the standard tiles, as in `RespectsAnchored`), the second to the same string translated by `v`.

The side of a doubled piece: `h^±` for the odd child, whose doubling is by `v_{q,1}` (horizontal stacking), and `v^±` for the
even child, whose doubling is by `v_{p,2}` (vertical stacking); the sign `+` is the forward side, `-` the reversed one. -/

namespace FLatticePaper.Tiles.DoublingRespect

open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Farey

/-- The side of a doubled piece: `h^+`/`h^-` (odd child, sign `true`/`false`) or `v^+`/`v^-` (even child). -/
def doublingSide (oddChild : Bool) (sign : Bool) : Side :=
  if oddChild then (if sign then Side.hPlus else Side.hMinus)
  else (if sign then Side.vPlus else Side.vMinus)

/-- The words of a register: for the register odometer of `regOdo` (the Boolean is `true` for the odd register), the word
`hWordOf u` of the tile `u` (the parity is that of the child of `u`), or the root tile (zero for odd, one for even). -/
def regWords (b : Bool) : Option Word → BinaryWord × BinaryWord
  | none => if b then ([Letter.p], [Letter.p]) else ([Letter.q], [Letter.q])
  | some u => (hWordOf u (!b), vWordOf u (!b))

/-- The tile-wise respect of the tile translation for the relevant side string (`def:partial_tile`, line 3375 applied to the
tiles of the string): for every placed tile `t` of the side string `sideString wh wv (0,0) s`, the second copy restricted to the
translate `t + v` has slope minus the slope of the first copy on `t` equal to `a_{n/d,i}`, and the domains of the two restrictions
are the tiles, the second translated by `v`. The restricted domains are the tiles of the string, so the respect is between
odometers on TILES (line 3375), not on the whole string. -/
def RespectsSideTranslation (n d : ℤ) (i : Bool) (wh wv : BinaryWord) (s : Side) (v : ℤ × ℤ)
    (o ostar : PartialOdometer) : Prop :=
  ∀ t ∈ sideString wh wv (0, 0) s,
    (∀ x ∈ tileShape t.1, x + t.2 ∈ o.dom) ∧
    (∀ x ∈ tileShape t.1, x + t.2 + v ∈ ostar.dom) ∧
    slopeOf ostar.val ((tileShape t.1).map (· + (t.2 + v))) - slopeOf o.val ((tileShape t.1).map (· + t.2)) =
      (((offsetA n d i).1 : ℚ), ((offsetA n d i).2 : ℚ))

end FLatticePaper.Tiles.DoublingRespect
