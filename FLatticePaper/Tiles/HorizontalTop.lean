import FLatticePaper.Tiles.ReflectedCover
import FLatticePaper.Tiles.HorizontalSides
import FLatticePaper.Tiles.HorizontalPair
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.CornerPositions

/-! S1 of the overlap form of H2, odd child: the top side of the translate of the odd tile is covered by the reversed horizontal
string. The translate is `P + v`, `v = -texV2 (fracOdd w)`, and its top side is `C - b` for `b` on the bottom walk, with
`C = sum(oddBottom) + sum(oddRight)`. The centre identity `C + v = lastPos + (2,0)` (from `hP_odd`, `centre_odd` and
`lastPos_hWordOf_false`) identifies the reflection of `ReflectedCover.cover_reflect` with the top side of the translate. -/

namespace FLatticePaper.Tiles.HorizontalTop

open FLatticePaper.Tiles FLatticePaper.Farey FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Construction FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.SiteInduction

/-- The centre identity of the odd child: `C + v = lastPos + (2,0)`, with `C` the half-turn centre and `v = -texV2 (fracOdd w)`. -/
theorem centre_identity_odd (w : Word) :
    F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) + (-texV2 (fracOdd w)) =
      lastPosOf (hStringAt (hWordOf w false) (0, 0)) + ((2 : ℤ), (0 : ℤ)) := by
  rw [FLatticePaper.Tiles.HorizontalPair.hP_odd w, FLatticePaper.Tiles.SiteHullOdd.centre_odd,
    FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_false, sum_oddBottom]
  have hc : curO w = fracOdd w := rfl
  rw [hc]
  ext <;> simp [texV1Odd, texV2] <;> omega

/-- **S1, odd child.** For every point `b` of the bottom walk, the point `C - b + v` of the top side of the translate lies in the
reversed horizontal tile list `hRevStringAt (hWordOf w false).reverse (1,-2)`. -/
theorem top_covered_odd (w : Word) (b : GInt) (hb : b ∈ F2Word.walk 0 (oddBottom w)) :
    tileCovers (hRevStringAt (hWordOf w false).reverse (1, -2))
      (F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) - b + (-texV2 (fracOdd w))) := by
  have hl := (FLatticePaper.Tiles.hWordOf_head_last w false).2
  have hc := FLatticePaper.Tiles.ReflectedCover.cover_reflect (hWordOf w false) .p none (1, -2) b hl
    (FLatticePaper.Tiles.HorizontalSides.bottom_covered_odd w b hb)
  have key := centre_identity_odd w
  have hpt : ((1 : ℤ), (-2 : ℤ)) + lastPosOf (hStringAt (hWordOf w false) (0, 0))
      + FLatticePaper.Tiles.ReflectedCover.shR .p - b
      = F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) - b + (-texV2 (fracOdd w)) := by
    rw [show F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) - b + (-texV2 (fracOdd w))
        = (F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) + (-texV2 (fracOdd w))) - b by abel, key]
    have h12 : ((1 : ℤ), (-2 : ℤ)) + ((1 : ℤ), (2 : ℤ)) = ((2 : ℤ), (0 : ℤ)) := by decide
    show ((1 : ℤ), (-2 : ℤ)) + lastPosOf (hStringAt (hWordOf w false) (0, 0)) + ((1 : ℤ), (2 : ℤ)) - b
      = lastPosOf (hStringAt (hWordOf w false) (0, 0)) + ((2 : ℤ), (0 : ℤ)) - b
    rw [show ((1 : ℤ), (-2 : ℤ)) + lastPosOf (hStringAt (hWordOf w false) (0, 0)) + ((1 : ℤ), (2 : ℤ)) - b
        = (((1 : ℤ), (-2 : ℤ)) + ((1 : ℤ), (2 : ℤ))) + lastPosOf (hStringAt (hWordOf w false) (0, 0)) - b by abel, h12]
    abel
  rw [← hpt]
  exact hc

/-- The centre identity of the even child: `C + v = lastPos + (2,0)`. -/
theorem centre_identity_even (w : Word) :
    F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) + (-texV2 (fracEven w)) =
      lastPosOf (hStringAt (hWordOf w true) (0, 0)) + ((2 : ℤ), (0 : ℤ)) := by
  rw [FLatticePaper.Tiles.HorizontalPair.hP_even w, FLatticePaper.Tiles.SiteHullEven.centre_even,
    FLatticePaper.Tiles.CornerPositions.lastPos_hWordOf_true, sum_evenBottom]
  have hc : curE w = fracEven w := rfl
  rw [hc]
  ext <;> simp [texV1Even, texV2] <;> omega

/-- **S1, even child.** For every point `b` of the bottom walk of the even tile, the point `C - b + v` of the top side of its
translate lies in the reversed horizontal tile list `hRevStringAt (hWordOf w true).reverse (1,-2)`. -/
theorem top_covered_even (w : Word) (b : GInt) (hb : b ∈ F2Word.walk 0 (evenBottom w)) :
    tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2))
      (F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) - b + (-texV2 (fracEven w))) := by
  have hl := (FLatticePaper.Tiles.hWordOf_head_last w true).2
  have hc := FLatticePaper.Tiles.ReflectedCover.cover_reflect (hWordOf w true) .p none (1, -2) b hl
    (FLatticePaper.Tiles.HorizontalSides.bottom_covered_even w b hb)
  have key := centre_identity_even w
  have hpt : ((1 : ℤ), (-2 : ℤ)) + lastPosOf (hStringAt (hWordOf w true) (0, 0))
      + FLatticePaper.Tiles.ReflectedCover.shR .p - b
      = F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) - b + (-texV2 (fracEven w)) := by
    rw [show F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) - b + (-texV2 (fracEven w))
        = (F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) + (-texV2 (fracEven w))) - b by abel, key]
    have h12 : ((1 : ℤ), (-2 : ℤ)) + ((1 : ℤ), (2 : ℤ)) = ((2 : ℤ), (0 : ℤ)) := by decide
    show ((1 : ℤ), (-2 : ℤ)) + lastPosOf (hStringAt (hWordOf w true) (0, 0)) + ((1 : ℤ), (2 : ℤ)) - b
      = lastPosOf (hStringAt (hWordOf w true) (0, 0)) + ((2 : ℤ), (0 : ℤ)) - b
    rw [show ((1 : ℤ), (-2 : ℤ)) + lastPosOf (hStringAt (hWordOf w true) (0, 0)) + ((1 : ℤ), (2 : ℤ)) - b
        = (((1 : ℤ), (-2 : ℤ)) + ((1 : ℤ), (2 : ℤ))) + lastPosOf (hStringAt (hWordOf w true) (0, 0)) - b by abel, h12]
    abel
  rw [← hpt]
  exact hc

end FLatticePaper.Tiles.HorizontalTop
