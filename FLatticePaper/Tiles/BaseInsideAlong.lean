import FLatticePaper.Tiles.BaseWalkSums
import FLatticePaper.Tiles.BaseHmAnchor
import FLatticePaper.Tiles.BaseVertVp

/-! # base_anchored_eq_along, odd 3^k: the anchored strings are the walk-placement strings

For the odd `3^k` word (`k = m+1`), the walk placement `alongStrings` at the corner `(0,0)` and the anchored placement
`anchoredStrings` (the four pieces of `RespectsAnchored`) are equal as lists. The two walk points of `alongStrings` are
`(0,0) + Σ gH` (after the first block) and `(0,0) + Σ gV + (0,-2)` (the reversed block); they are the anchors `lastPosOf` of
the horizontal and vertical pieces. The sums are `sum_gH_ladder` and `sum_gV_ladder`, the anchors `anchor_three` and
`anchor_hm_odd`. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.BaseHmAnchor FLatticePaper.Tiles.BaseVertVp
open FLatticePaper.Tiles.BaseHmOdd

theorem ladderH_eq_wL (k : ℕ) : ladderH k = FLatticePaper.Tiles.BaseHpLadder.wL k := by
  simp [ladderH, FLatticePaper.Tiles.BaseHpLadder.wL]

theorem base_anchored_eq_along_odd (m : ℕ) :
    anchoredStrings (hWordOf (List.replicate (m + 1) Digit.three) false)
        (vWordOf (List.replicate (m + 1) Digit.three) false) (0, 0) =
      alongStrings (hWordOf (List.replicate (m + 1) Digit.three) false)
        (vWordOf (List.replicate (m + 1) Digit.three) false) (0, 0) := by
  have hV : vWordOf (List.replicate (m + 1) Digit.three) false = ladderV (m + 1) :=
    FLatticePaper.Tiles.BaseVertPiece.vWordOf_three_false (m + 1)
  have hH : hWordOf (List.replicate (m + 1) Digit.three) false = ladderH (m + 1) := by
    rw [FLatticePaper.Tiles.BaseHpLadder.hWordOf_three_false, ladderH_eq_wL]
  have h1 : lastPosOf (vRevStringAt (ladderV (m + 1)).reverse (0, 0))
      = (0, 0) + (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) + (0, -2) := by
    have h := anchor_hm_odd (m + 1) (by omega)
    rw [hV] at h
    rw [h]
    simp [posHm]
    constructor <;> ring
  have h2 : lastPosOf (hStringAt (ladderH (m + 1)) (0, 0)) = (0, 0) + (4 * (m : ℤ) + 8, 1) + (-1, 0) := by
    rw [← hH]
    have hA := anchor_three (m + 1)
    rw [hA]
    ext
    · simp
      ring
    · simp
  rw [hV, hH]
  unfold anchoredStrings alongStrings
  dsimp only [gPseudo]
  rw [walkAt_total, walkAt_gH, sum_gH_ladder m, sum_gV_ladder m, h1, h2]

end FLatticePaper.Tiles
