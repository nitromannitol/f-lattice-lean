import FLatticePaper.Tiles.AltItem3
import FLatticePaper.Tiles.ReflectedCoverConverse

/-! # Item (3) of `lemma:alternate_tile_properties`: the two strings given by the half-turn, and the pseudo-squares

Surgical edition 3243bef, Step 2 of the proof of `lemma:alternate_tile_properties`, the table of (3): with
`(A, B, U, V) = (v_{p₁,1}, v_{p₁,2}, v_{q₁,1}, v_{q₁,2})` and `c(T̂) = 0`, the reversed horizontal string of `T̂(q₀)` starts at
`2B + V - U + 1 - 2i` (even-first) or `2B + V + U + 1 - 2i` (odd-first), and the forward vertical string of `T̂(p₀)` at
`A + B + 2U - 1 - i` (even-first) or `A + U - 1 - i` (odd-first). The even-first orientation is `W₁` even
(`phase w ≠ 1`).

These strings are the half-turns of the strings of `AltItem3` about the centres `D` of the tiles (`AltPieces.altEven_halfTurn`,
`altOdd_halfTurn`): the reversed horizontal string of a word at `c` is the reflection of its forward string at `0` through
`c + lastPos + shR p` (`ReflectedCoverConverse.placed_hRev_iff`), and the forward vertical string at `a` is the reflection of
the reversed vertical string at `s` through `a + lastPos + shR q + s` (`ReflectedCoverConverse.placed_vRev_iff`); the end
positions are those of the standard tiles of the children (`StdCornerAnchors`). -/

namespace FLatticePaper.Tiles.AltItem3

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)

/-- The start of the reversed horizontal string of `T̂(q₀)`: `2B + V ∓ U + 1 - 2i`. -/
def revHOff (w : Word) : Site :=
  2 • texV2 (parentsAt w).odd + texV2 (parentsAt w).even +
    (if phase w == 1 then texV1Even (parentsAt w).even else -texV1Even (parentsAt w).even) + (1, -2)

/-- The start of the forward vertical string of `T̂(p₀)`: `A + B + 2U - 1 - i` or `A + U - 1 - i`. -/
def fwdVOff (w : Word) : Site :=
  texV1Odd (parentsAt w).odd + texV1Even (parentsAt w).even +
    (if phase w == 1 then 0 else texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) + (-1, -1)

theorem revHOff_centre (w : Word) :
    revHOff w + lastPosOf (hStringAt (hWordOf w true) (0, 0)) + ReflectedCover.shR Letter.p =
      centreEven (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
  rw [StdCornerAnchors.stdAnchorX_even]
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;>
    simp only [revHOff, centreEven, h, if_true, if_false, Bool.false_eq_true, ReflectedCover.shR,
      StandardClause.fracEven, Parents.current, Parents.combine, texV1Even, texV2] <;>
    ext <;> simp <;> ring

theorem fwdVOff_centre (w : Word) :
    fwdVOff w + lastPosOf (vStringAt (vWordOf w false) (0, 0)) + ReflectedCover.shR Letter.q + SurgicalAlt.altOffsetS w =
      centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even := by
  rw [StdCornerAnchors.stdAnchorC_of (vWordOf w false) (StandardClause.fracOdd w).num (StandardClause.fracOdd w).den
    (StringCorners.vertWord_head_last w).1 (vertWord_counts w).1 (vertWord_counts w).2]
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;>
    simp only [fwdVOff, centreOdd, SurgicalAlt.altOffsetS, h, if_true, if_false, Bool.false_eq_true,
      ReflectedCover.shR, StandardClause.fracOdd, Parents.current, Parents.combine, texV1Odd, texV1Even, texV2] <;>
    ext <;> simp <;> ring

/-- **The reversed horizontal string of `T̂(q₀)`**, of `rev(w_h(q₀))` at `2B + V ∓ U + 1 - 2i`, lies in `T̂(q₀)`. -/
theorem item3_revH {w : Word} (hw : ¬ IsBase w) :
    InsideTile {x | x ∈ altEvenTile AltRotStep.B w} (hRevStringAt (hWordOf w true).reverse (revHOff w)) := by
  intro x hx
  rw [ReflectedCoverConverse.placed_hRev_iff _ Letter.p (hWordOf_head_last w true).2, revHOff_centre] at hx
  have hy := (altEven_halfTurn w _).1 (item3_fwdH AltRotStep.B hw _ hx)
  rwa [sub_sub_cancel] at hy

/-- **The forward vertical string of `T̂(p₀)`**, of `w_v(p₀)` at `A + B + 2U - 1 - i` or `A + U - 1 - i`, lies in `T̂(p₀)`. -/
theorem item3_fwdV {w : Word} (hw : ¬ IsBase w) :
    InsideTile {x | x ∈ altOddTile AltRotStep.B w} (vStringAt (vWordOf w false) (fwdVOff w)) := by
  intro z hz
  have h := (ReflectedCoverConverse.placed_vRev_iff (vWordOf w false) Letter.q (StringCorners.vertWord_head_last w).2
    (fwdVOff w) (SurgicalAlt.altOffsetS w)
    (fwdVOff w + lastPosOf (vStringAt (vWordOf w false) (0, 0)) + ReflectedCover.shR Letter.q +
      SurgicalAlt.altOffsetS w - z)).2 (by rwa [sub_sub_cancel])
  have hy := (altOdd_halfTurn w _).1 (item3_revV AltRotStep.B hw _ h)
  rwa [fwdVOff_centre, sub_sub_cancel] at hy

/-- **Item (3), even alternate child**: `T̂(q₀)` is a `w_h(q₀)`-pseudo-square with `c(T₁) = c(T̂) = 0` for the first tile `T₁`
of `w_h(q₀)`, the reversed string at `2B + V ∓ U + 1 - 2i`. -/
theorem alt_item3_even {w : Word} (hw : ¬ IsBase w) :
    InsideTile {x | x ∈ altEvenTile AltRotStep.B w} (hPartialTiles (hWordOf w true) (0, 0) (revHOff w)) ∧
      ((hStringAt (hWordOf w true) (0, 0)).headD (ZTile.zero, 0)).2 = (0, 0) := by
  refine ⟨fun x hx => ?_, alt_item3a _ _ ?_⟩
  · rw [hPartialTiles, placedSites_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact item3_fwdH AltRotStep.B hw x hx
    · exact item3_revH hw x hx
  · intro h
    have := (hWordOf_head_last w true).2
    rw [h] at this
    simp at this

/-- **Item (3), odd alternate child**: `T̂(p₀)` is a `w_v(p₀)`-pseudo-square with `c(T₁') = c(T̂) + s` for the first tile `T₁'`
of `rev(w_v(p₀))` (`s = 0` even-first, `s = -U + B` odd-first), the forward string at `A + B + 2U - 1 - i` or
`A + U - 1 - i`. -/
theorem alt_item3_odd {w : Word} (hw : ¬ IsBase w) :
    InsideTile {x | x ∈ altOddTile AltRotStep.B w}
        (vPartialTiles (vWordOf w false) (SurgicalAlt.altOffsetS w) (fwdVOff w)) ∧
      ((vRevStringAt (vWordOf w false).reverse (SurgicalAlt.altOffsetS w)).headD (ZTile.zero, 0)).2 =
        SurgicalAlt.altOffsetS w := by
  refine ⟨fun x hx => ?_, alt_item3b _ _ ?_⟩
  · rw [vPartialTiles, placedSites_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact item3_revV AltRotStep.B hw x hx
    · exact item3_fwdV hw x hx
  · intro h
    have := (StringCorners.vertWord_head_last w).2
    rw [List.reverse_eq_nil_iff] at h
    rw [show vertWord w = vWordOf w false from rfl, h] at this
    simp at this

end FLatticePaper.Tiles.AltItem3
