import FLatticePaper.Tiles.BaseInsideAlong
import FLatticePaper.Tiles.StandardBaseBridge
import FLatticePaper.Tiles.PartialBoundary

/-! # InsideTile for the odd 3^k base odometer

The placed sites of the four strings of `RespectsAnchored` (the anchored placement at `(0,0)`) lie in the paper ladder tile
`paperLadderTile (2k+2)`: by `base_anchored_eq_along_odd` they are the walk-placement sites, which `ladder_contain` places in the tile.
With `mem_ladderF_iff_paper`, this is `InsideTile` for the domain `ladderF (2k+2)` of the odd `3^k` odometer. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.BaseHmAnchor FLatticePaper.Tiles.BaseVertVp
open FLatticePaper.Construction FLatticePaper.Tiles.Standard

theorem anchored_contain_odd (m : ℕ) (x : GInt)
    (hx : x ∈ placedSites (anchoredStrings (hWordOf (List.replicate (m + 1) Digit.three) false)
      (vWordOf (List.replicate (m + 1) Digit.three) false) (0, 0))) :
    x ∈ paperLadderTile (2 * (m : ℤ) + 4) := by
  rw [base_anchored_eq_along_odd] at hx
  have hV : vWordOf (List.replicate (m + 1) Digit.three) false = ladderV (m + 1) :=
    FLatticePaper.Tiles.BaseVertPiece.vWordOf_three_false (m + 1)
  have hH : hWordOf (List.replicate (m + 1) Digit.three) false = ladderH (m + 1) := by
    rw [FLatticePaper.Tiles.BaseHpLadder.hWordOf_three_false, ladderH_eq_wL]
  rw [hV, hH] at hx
  exact ladder_contain m x hx

theorem insideTile_odd (m : ℕ) :
    InsideTile ((ladderF (2 * ((m + 1 : ℕ) : ℤ) + 2) : Finset GInt) : Set GInt)
      (hStringAt (hWordOf (List.replicate (m + 1) Digit.three) false) (0, 0) ++
        hRevStringAt (hWordOf (List.replicate (m + 1) Digit.three) false).reverse
          (lastPosOf (vRevStringAt (vWordOf (List.replicate (m + 1) Digit.three) false).reverse (0, 0))) ++
        vRevStringAt (vWordOf (List.replicate (m + 1) Digit.three) false).reverse (0, 0) ++
        vStringAt (vWordOf (List.replicate (m + 1) Digit.three) false)
          (lastPosOf (hStringAt (hWordOf (List.replicate (m + 1) Digit.three) false) (0, 0)))) := by
  intro x hx
  rw [Finset.mem_coe, mem_ladderF_iff_paper (by push_cast; omega)]
  have e : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [e]
  exact anchored_contain_odd m x hx

end FLatticePaper.Tiles
